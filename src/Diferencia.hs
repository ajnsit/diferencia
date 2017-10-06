{-# LANGUAGE DeriveFunctor       #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Diferencia where

import           Data.IntMap   (IntMap)
import qualified Data.IntMap   as IM

import           Data.Align    (Align, alignWith)
import qualified Data.Align    as A
import           Data.List     (sortOn)
import           Data.These    (These (..))

import qualified Data.MemoTrie as M
import qualified Data.Vector   as V

-- A Recursive Expression
-- f: Functor
-- Note: Recursion means that I can't derive generic instances (Like Eq) for Expr
--       (because UndecidableInstances)
newtype Expr f = Expr { unExpr :: f (Expr f) }


-- A Primitive edit
data PrimEdit a b
  -- Do nothing
  = Nop a
  -- Delete the node
  | Delete a
  -- Replace the node
  | Replace a b
  -- Add new "Child" nodes.
  | Insert b
  deriving (Eq, Show)

-- Generic Edit Operation on a Functor Node (a -> b)
-- a: Current nodes
-- b: New nodes
-- f: Shape of the nodes
-- c: Continuation edit operation
data Edit a b f c
  = PrimEdit (PrimEdit a b)
  -- Structure specific edit of the "contents" of the node.
  | Edit (f c)
  deriving (Eq, Show, Functor)

-- An Edit Operation on a structure.
type Editor f = Expr (Edit () (Expr f) f)

-- Edit Operation which includes the original State of the structure.
-- Conceptually it's (Expr f, Editor f), but typesafe so Expr and Editor have matching shapes.
type EditState f = Expr (Edit (Expr f) (Expr f) f)

-- Class of expressions that have an "Empty" element
-- class Empty f where
--   empty :: Expr f

-- Nil Expression
nilExpr :: Align f => Expr f
nilExpr = Expr A.nil

-- Class of expressions that can be diffed
class Diffable f where
  -- base expr -> new expr -> edit state
  diffExpr :: Expr f -> Expr f -> EditState f

-- NOTE: ATTRIBUTION: diffList, diffKeys, and diffBy in this file are adapted from the tree-diff package

-- Diff within a list
diffList :: (Eq (Expr f), Diffable f) => [Expr f] -> [Expr f] -> [EditState f]
diffList l1 l2 = map diffReplacement (diffBy (==) l1 l2)
  where
    diffReplacement (Nop z)       = Expr (PrimEdit (Nop z))
    diffReplacement (Insert x)    = Expr (PrimEdit (Insert x))
    diffReplacement (Delete y)    = Expr (PrimEdit (Delete y))
    diffReplacement (Replace x y) = diffExpr x y

diffBy :: (a -> a -> Bool) -> [a] -> [a] -> [PrimEdit a a]
diffBy eq xs' ys' = reverse (snd (lcs (V.length xs) (V.length ys)))
  where
    xs = V.fromList xs'
    ys = V.fromList ys'

    lcs = M.memo2 impl

    -- impl :: Int -> Int -> (Int, [PrimEdit a a])
    impl 0 0 = ((0::Int), [])
    impl 0 m = case lcs 0 (m-1) of
        (w, e) -> (w + 1, Insert (ys V.! (m - 1)) : e)
    impl n 0 = case lcs (n -1) 0 of
        (w, e) -> (w + 1, Delete (xs V.! (n - 1)) : e)

    impl n m = head $ sortOn fst
        [ e
        , bimap (+1) (Insert y :) (lcs n (m - 1))
        , bimap (+1) (Delete x :) (lcs (n - 1) m)
        ]
      where
        x = xs V.! (n - 1)
        y = ys V.! (m - 1)

        e | eq x y    = bimap id   (Nop x :)   (lcs (n - 1) (m - 1))
          | otherwise = bimap (+1) (Replace x y :) (lcs (n -1 ) (m - 1))

bimap :: (a -> c) -> (b -> d) -> (a, b) -> (c, d)
bimap f g (x, y) = (f x, g y)

-- Diff within a map
diffKeys :: Diffable f => IntMap (Expr f) -> IntMap (Expr f) -> IntMap (EditState f)
diffKeys m1 m2 = IM.unions [cs, as, bs]
  where
    cs = IM.intersectionWith diffExpr m1 m2
    as = Expr . PrimEdit . Delete <$> IM.difference m1 cs
    bs = Expr . PrimEdit . Insert <$> IM.difference m2 cs

-- Edit a Tree
-- current state -> conceptually pure edit (to be applied) -> (new state, actual commuted edit)
-- This is kinda like a state monad
edit :: (Diffable f, Align f) => EditState f -> Editor f -> (EditState f, Editor f)
-- NOP --
-- If the tree has not been modified yet, init state
edit (Expr (PrimEdit (Nop t))) te = (wrapState t te, te)
-- Nop means revert the previous edit
edit t (Expr (PrimEdit (Nop ()))) = (resetExpr t, extractEdit (revertEdit t))
-- INSERT --
-- When inserting an expression, diff for differences
edit (Expr (PrimEdit (Insert b1))) (Expr (PrimEdit (Insert b2))) = (Expr (PrimEdit (Insert b2)), extractEdit (diffExpr b1 b2))
-- TODO: NEEDS DISCUSSION: NOTE: Here we think of replacing something on top of a non-existing node as an insert.
edit (Expr (PrimEdit (Insert _))) (Expr (PrimEdit (Replace () b2))) = (Expr (PrimEdit (Insert b2)), Expr (PrimEdit (Replace () b2)))
-- For all other cases, when something was newly inserted (didn't exist earlier), editing does nothing
edit (Expr (PrimEdit (Insert _))) _  = (keep nilExpr, Expr (PrimEdit (Delete ())))
-- DELETE --
-- Deleting the same thing twice has no effect
edit ts@(Expr (PrimEdit (Delete _))) (Expr (PrimEdit (Delete ()))) = (ts, pass)
-- When something was deleted earlier, special cases for efficiency
-- TODO: NEEDS DISCUSSION: NOTE: Here we think of inserting something on top of an existing node as a replace.
edit (Expr (PrimEdit (Delete t))) te@(Expr (PrimEdit (Insert b))) = (Expr (PrimEdit (Replace t b)), te)
-- Delete and replace is just replace
edit (Expr (PrimEdit (Delete t))) te@(Expr (PrimEdit (Replace () b))) = (Expr (PrimEdit (Replace t b)), te)
-- When something was deleted earlier, we insert the modified expr directly
edit (Expr (PrimEdit (Delete t))) te = let es = wrapState t te in (es, Expr (PrimEdit (Insert (extractExpr es))))
-- REPLACE --
-- Replacing things twice, diff for differences
edit (Expr (PrimEdit (Replace a b1))) (Expr (PrimEdit (Replace () b2))) = (Expr (PrimEdit (Replace a b2)), extractEdit (diffExpr b1 b2))
-- TODO: NEEDS DISCUSSION: NOTE: Here we think of inserting something on top of an existing node as a replace.
edit (Expr (PrimEdit (Replace a b1))) (Expr (PrimEdit (Insert b2))) = (Expr (PrimEdit (Replace a b2)), extractEdit (diffExpr b1 b2))
-- Replacement and then deletion is basically deletion
edit (Expr (PrimEdit (Replace a _))) te@(Expr (PrimEdit (Delete ()))) = (Expr (PrimEdit (Delete a)), te)
-- This is the tricky one. We could have simply replaced nodes, but the point is to make modifications fine grained.
--  TODO: So eventually we should translate the edits made to the original structure, to the replaced structure.
--  For now, we wield the replacing nodes hammer.
edit (Expr (PrimEdit (Replace a _))) te =
  let orig = wrapState a te
  in (orig, Expr (PrimEdit (Replace () (extractExpr orig))))
-- EDIT --
-- Delete a previously modified node
-- Here the (sorta) expensive operation is extracting the original expression from the edits
-- TODO: Perhaps we should cache a copy of the original expression with edits.
--       But we can't lose type safety. So if we store it as Edit c t, we must ensure `t == extractExpr c` at all times.
--       Perhaps use MemoTrie for this.
edit ts@(Expr (Edit _)) te@(Expr (PrimEdit (Delete ()))) = (Expr (PrimEdit (Delete (extractExpr ts))), te)
-- Replace a previously modified node
edit ts@(Expr (Edit _)) te@(Expr (PrimEdit (Replace () b))) = (Expr (PrimEdit (Replace (extractExpr ts) b)), te)
-- TODO: NEEDS DISCUSSION: NOTE: Here we think of inserting something on top of an existing node as a replace.
edit ts@(Expr (Edit _)) te@(Expr (PrimEdit (Insert b))) = (Expr (PrimEdit (Replace (extractExpr ts) b)), te)
-- The money shot. Structurally diff edits.
edit (Expr (Edit c1)) (Expr (Edit c2)) =
  let x = alignWith zipDiffState c1 c2
  in (Expr (Edit (fmap fst x)), Expr (Edit (fmap snd x)))

-- Zip up two successive edits
zipDiffState :: (Diffable f, Align f)
  => These (Expr (Edit (Expr f) (Expr f) f)) (Expr (Edit () (Expr f) f))
  -> (,)   (Expr (Edit (Expr f) (Expr f) f)) (Expr (Edit () (Expr f) f))
-- An edited node that's left alone
zipDiffState (This t)    = (t, pass)
-- Editing a non existent node, does nothing
zipDiffState (That _)    = (keep nilExpr, pass)
-- If both edit ops exist, recurse
zipDiffState (These t e) = edit t e

-- Convert an Editor to a State, by merging in the original expression.
-- `Expr` and `Editor` may not have matching structure. But they are forced to match by using nilExpr.
wrapState :: Align f => Expr f -> Editor f -> EditState f
wrapState t@(Expr t') (Expr e) = Expr $ case e of
  PrimEdit (Nop ())       -> PrimEdit (Nop t)
  PrimEdit (Delete ())    -> PrimEdit (Delete t)
  PrimEdit (Replace () b) -> PrimEdit (Replace t b)
  PrimEdit (Insert b)     -> PrimEdit (Insert b)
  Edit c                  -> Edit (alignWith zipState t' c)

-- Zip a non-exclusive union of Tree and Editor.
zipState :: Align f => These (Expr f) (Expr (Edit () (Expr f) f)) -> Expr (Edit (Expr f) (Expr f) f)
-- Assume, that lack of an editor means no change
zipState (This t)    = keep t
-- Editing a non existing node, is same as operating on nilExpr
zipState (That e)    = wrapState nilExpr e
-- If we have both a tree and an editor then combine them with wrapState
zipState (These t e) = wrapState t e

-- Extract the editor from the edit state
extractEdit :: Functor f => EditState f -> Editor f
extractEdit (Expr x) = Expr $ case x of
  PrimEdit (Nop _)       -> PrimEdit (Nop ())
  PrimEdit (Delete _)    -> PrimEdit (Delete ())
  PrimEdit (Replace _ b) -> PrimEdit (Replace () b)
  PrimEdit (Insert b)    -> PrimEdit (Insert b)
  Edit c                 -> Edit $ fmap extractEdit c

-- Extract the original expr from the edit state
extractExpr :: Align f => EditState f -> Expr f
extractExpr (Expr x) = case x of
  PrimEdit (Nop t)       -> t
  PrimEdit (Delete t)    -> t
  PrimEdit (Replace t _) -> t
  PrimEdit (Insert _)    -> nilExpr
  Edit c                 -> Expr $ fmap extractExpr c

-- Keep the underlying expression the same, but change the edit to Nop
resetExpr :: Align f => EditState f -> EditState f
resetExpr (Expr t') = case t' of
  PrimEdit (Nop t)       -> keep t
  PrimEdit (Delete t)    -> keep t
  PrimEdit (Replace t _) -> keep t
  PrimEdit (Insert _)    -> keep nilExpr
  Edit c                 -> Expr (Edit (fmap resetExpr c))

-- Compute an edit operation which, when applied, will revert existing edits
revertEdit :: Functor f => EditState f -> EditState f
revertEdit (Expr e) = Expr $ case e of
  PrimEdit (Nop t)       -> PrimEdit (Nop t)
  PrimEdit (Delete t)    -> PrimEdit (Insert t)
  PrimEdit (Replace t b) -> PrimEdit (Replace b t)
  PrimEdit (Insert a)    -> PrimEdit (Delete a)
  Edit c                 -> Edit $ fmap revertEdit c

-- Frequently used shortcuts

-- Primitive Editor constructors
eNop, pass :: Editor f
eNop = Expr (PrimEdit (Nop ()))
pass = eNop
eDel :: Editor f
eDel = Expr (PrimEdit (Delete ()))
eIns :: Expr f -> Editor f
eIns a = Expr (PrimEdit (Insert a))
eRep :: Expr f -> Editor f
eRep b = Expr (PrimEdit (Replace () b))

-- Primitive edit state constructors
esNop, keep :: Expr f -> EditState f
esNop a = Expr (PrimEdit (Nop a))
keep a = esNop a
esDel :: Expr f -> EditState f
esDel a = Expr (PrimEdit (Delete a))
esIns :: Expr f -> EditState f
esIns a = Expr (PrimEdit (Insert a))
esRep :: Expr f -> Expr f -> EditState f
esRep a b = Expr (PrimEdit (Replace a b))
