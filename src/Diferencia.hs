{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE DeriveFunctor       #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving  #-}
{-# LANGUAGE TypeFamilies        #-}
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

-- A Primitive edit operation
data PrimEditOp a b
  -- Do nothing
  = Nop a
  -- Delete the node
  | Delete a
  -- Replace the node
  | Replace a b
  -- Add new "Child" nodes.
  | Insert b
  deriving (Eq, Show)

-- We need this class to avoid using functions (f a -> f a) in Edit
class NodeEditable (f :: * -> *) where
  type NodeEditOp f
  editNode       :: forall a. f a -> NodeEditOp f -> f a
  revertNodeEdit :: forall a. f a -> NodeEditOp f -> NodeEditOp f

-- Shortcut
calcRevertNodeEdit :: (NodeEditable f, Align f) => NodeEditOp f -> EditState f -> NodeEditOp f
calcRevertNodeEdit n c = revertNodeEdit (unExpr (extractOriginal c)) n

-- Generic Edit Operation on a Functor Node (a -> b)
-- a: Current nodes
-- b: New nodes
-- f: Shape of the nodes
-- c: Continuation edit operation
data Edit a b f c
  = PrimEdit (PrimEditOp a b)
  -- Custom edit of the node data.
  | NodeEdit (NodeEditOp f) c
  -- Structure specific edit of the "contents" of the node.
  | Edit (f c)

deriving instance (Eq a, Eq b, Eq (f c), Eq c, Eq (NodeEditOp f)) => Eq (Edit a b f c)
deriving instance (Show a, Show b, Show c, Show (f c), Show (NodeEditOp f)) => Show (Edit a b f c)

-- deriving (Eq, Show, Functor)

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

-- Our requirement for an expression functor
type Expression f =
  ( Diffable f
  , NodeEditable f
  , Eq (Expr f)
  , Align f
  )

-- NOTE: ATTRIBUTION: diffList, diffKeys, and diffBy in this file are adapted from the tree-diff package

-- Diff within a list
diffList :: (Eq (Expr f), Diffable f) => [Expr f] -> [Expr f] -> [EditState f]
diffList l1 l2 = map diffReplacement (diffBy (==) l1 l2)
  where
    diffReplacement (Nop z)       = Expr (PrimEdit (Nop z))
    diffReplacement (Insert x)    = Expr (PrimEdit (Insert x))
    diffReplacement (Delete y)    = Expr (PrimEdit (Delete y))
    diffReplacement (Replace x y) = diffExpr x y

diffBy :: (a -> a -> Bool) -> [a] -> [a] -> [PrimEditOp a a]
diffBy eq xs' ys' = reverse (snd (lcs (V.length xs) (V.length ys)))
  where
    xs = V.fromList xs'
    ys = V.fromList ys'

    lcs = M.memo2 impl

    -- impl :: Int -> Int -> (Int, [PrimEditOp a a])
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
-- Many things here are lazy on purpose to avoid computing things which will be overwritten anyways.
-- TODO: However successive edits will accumulate thunks.
edit :: (Diffable f, NodeEditable f, Align f) => EditState f -> Editor f -> (EditState f, Editor f)
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
edit (Expr (PrimEdit (Delete t))) te = let es = wrapState t te in (es, Expr (PrimEdit (Insert (extractModified es))))
-- REPLACE --
-- Replacing things twice, diff for differences
edit (Expr (PrimEdit (Replace a b1))) (Expr (PrimEdit (Replace () b2))) = (Expr (PrimEdit (Replace a b2)), extractEdit (diffExpr b1 b2))
-- TODO: NEEDS DISCUSSION: NOTE: Here we think of inserting something on top of an existing node as a replace.
edit (Expr (PrimEdit (Replace a b1))) (Expr (PrimEdit (Insert b2))) = (Expr (PrimEdit (Replace a b2)), extractEdit (diffExpr b1 b2))
-- Replacement and then deletion is basically deletion
edit (Expr (PrimEdit (Replace a _))) te@(Expr (PrimEdit (Delete ()))) = (Expr (PrimEdit (Delete a)), te)
-- The Edit is tricky. We could have simply replaced nodes, but the point is to make modifications fine grained.
-- The CustomEdit case is mostly correct (children need to be replaced), but we ideally can keep the parent node and apply node edits.
--  TODO: So eventually we should translate the edits made to the original structure, to the replaced structure, in both cases.
--  For now, we wield the replacing nodes hammer.
edit (Expr (PrimEdit (Replace a _))) te =
  let orig = wrapState a te
  in (orig, Expr (PrimEdit (Replace () (extractModified orig))))
-- EDIT --
-- Delete a previously modified node
-- Here the (sorta) expensive operation is extracting the original expression from the edits
-- TODO: Perhaps we should cache a copy of the original expression with edits.
--       But we can't lose type safety. So if we store it as Edit c t, we must ensure `t == extractOriginal c` at all times.
--       Perhaps use MemoTrie for this.
edit ts@(Expr (Edit _)) te@(Expr (PrimEdit (Delete ()))) = (Expr (PrimEdit (Delete (extractOriginal ts))), te)
-- Replace a previously modified node
edit ts@(Expr (Edit _)) te@(Expr (PrimEdit (Replace () b))) = (Expr (PrimEdit (Replace (extractOriginal ts) b)), te)
-- TODO: NEEDS DISCUSSION: NOTE: Here we think of inserting something on top of an existing node as a replace.
edit ts@(Expr (Edit _)) te@(Expr (PrimEdit (Insert b))) = (Expr (PrimEdit (Replace (extractOriginal ts) b)), te)
-- The money shot. Structurally diff edits.
edit (Expr (Edit c1)) (Expr (Edit c2)) =
  let x = alignWith zipDiffState c1 c2
  in (Expr (Edit (fmap fst x)), Expr (Edit (fmap snd x)))
-- For all other edits (i.e. NodeEdit), we simply replace nodes
--  TODO: Eventually we should be able to delete children and apply node edits to the parent.
edit ts@(Expr (Edit _)) te =
  let orig = extractOriginal ts
      final = extractModified (wrapState orig te)
  in (Expr (PrimEdit (Replace orig final)), Expr (PrimEdit (Replace () final)))
-- NODE EDIT --
-- Editing node, and then deleting node, is the same as delete
edit (Expr (NodeEdit _ c)) (Expr (PrimEdit (Delete ()))) = (Expr (PrimEdit (Delete (extractOriginal c))), Expr (PrimEdit (Delete ())))
-- TODO: NEEDS DISCUSSION: NOTE: Here we think of inserting something on top of an existing node as a replace.
edit (Expr (NodeEdit _ c)) (Expr (PrimEdit (Insert n))) = (Expr (PrimEdit (Replace (extractOriginal c) n)), Expr (PrimEdit (Replace () n)))
-- Editing node, and then replacing node, is the same as replace
edit (Expr (NodeEdit _ c)) (Expr (PrimEdit (Replace () b))) = (Expr (PrimEdit (Replace (extractOriginal c) b)), Expr (PrimEdit (Replace () b)))
-- If we edit nodes, and then edit children, revert node edit and merge child edits.
edit (Expr (NodeEdit n c1)) c2@(Expr (Edit _)) =
  let (cs, ce) = edit c1 c2
  in (cs, Expr (NodeEdit (calcRevertNodeEdit n c1) ce))
-- Similar procedure of merging, for multiple node edits.
edit (Expr (NodeEdit n1 c1)) (Expr (NodeEdit n2 c2)) =
  let (cs, ce) = edit c1 c2
  in (Expr (NodeEdit n2 cs), Expr (NodeEdit (calcRevertNodeEdit n1 c1) ce))

-- Zip up two successive edits
zipDiffState :: (Diffable f, NodeEditable f, Align f)
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
  NodeEdit n c            -> NodeEdit n (wrapState t c)
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
  NodeEdit n c           -> NodeEdit n (extractEdit c)
  Edit c                 -> Edit $ fmap extractEdit c

-- Extract the original expr from the edit state
extractOriginal :: Align f => EditState f -> Expr f
extractOriginal (Expr x) = case x of
  PrimEdit (Nop t)       -> t
  PrimEdit (Delete t)    -> t
  PrimEdit (Replace t _) -> t
  PrimEdit (Insert _)    -> nilExpr
  NodeEdit _ c           -> extractOriginal c
  Edit c                 -> Expr (fmap extractOriginal c)

-- Extract the modified expr from the edit state
extractModified :: (NodeEditable f, Align f) => EditState f -> Expr f
extractModified (Expr x) = case x of
  PrimEdit (Nop t)       -> t
  PrimEdit (Delete _)    -> nilExpr
  PrimEdit (Replace _ b) -> b
  PrimEdit (Insert b)    -> b
  NodeEdit n c           -> Expr (editNode (unExpr (extractModified c)) n)
  Edit c                 -> Expr (fmap extractModified c)

-- Keep the underlying expression the same, but change the edit to Nop
resetExpr :: Align f => EditState f -> EditState f
resetExpr (Expr t') = case t' of
  PrimEdit (Nop t)       -> keep t
  PrimEdit (Delete t)    -> keep t
  PrimEdit (Replace t _) -> keep t
  PrimEdit (Insert _)    -> keep nilExpr
  NodeEdit _ c           -> keep (extractOriginal c)
  Edit c                 -> Expr (Edit (fmap resetExpr c))

-- Compute an edit operation which, when applied, will revert existing edits
revertEdit :: (NodeEditable f, Align f) => EditState f -> EditState f
revertEdit (Expr e) = Expr $ case e of
  PrimEdit (Nop t)       -> PrimEdit (Nop t)
  PrimEdit (Delete t)    -> PrimEdit (Insert t)
  PrimEdit (Replace t b) -> PrimEdit (Replace b t)
  PrimEdit (Insert a)    -> PrimEdit (Delete a)
  NodeEdit n c           -> NodeEdit (calcRevertNodeEdit n c) (revertEdit c)
  Edit c                 -> Edit $ fmap revertEdit c

-- Frequently used shortcuts

-- Editor constructors
eNop, pass :: Editor f
eNop = Expr (PrimEdit (Nop ()))
pass = eNop
eDel :: Editor f
eDel = Expr (PrimEdit (Delete ()))
eIns :: Expr f -> Editor f
eIns a = Expr (PrimEdit (Insert a))
eRep :: Expr f -> Editor f
eRep b = Expr (PrimEdit (Replace () b))
eEdit :: f (Editor f) -> Editor f
eEdit f = Expr (Edit f)
eNodeEdit :: NodeEditOp f -> Editor f -> Editor f
eNodeEdit n c = Expr (NodeEdit n c)

-- Edit state constructors
esNop, keep :: Expr f -> EditState f
esNop a = Expr (PrimEdit (Nop a))
keep a = esNop a
esDel :: Expr f -> EditState f
esDel a = Expr (PrimEdit (Delete a))
esIns :: Expr f -> EditState f
esIns a = Expr (PrimEdit (Insert a))
esRep :: Expr f -> Expr f -> EditState f
esRep a b = Expr (PrimEdit (Replace a b))
esEdit :: f (EditState f) -> EditState f
esEdit f = Expr (Edit f)
esNodeEdit :: NodeEditOp f -> EditState f -> EditState f
esNodeEdit n c = Expr (NodeEdit n c)
