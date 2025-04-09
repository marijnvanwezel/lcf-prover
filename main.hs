module Main where

import Data.Set (Set)
import qualified Data.Set as Set

------------------------
-- 1. Inference rules --
------------------------

data Formula
  = VarF !Int              -- x₁, x₂, ...
  | ImpF !Formula !Formula -- A → B
  deriving (Eq, Ord)

data Theorem
  = Theorem !(Set Formula) !Formula -- Γ ⊢ A

--
-- ─────
-- A ⊢ A
assume :: Formula -> Theorem
assume a = Theorem (Set.singleton a) a

--      Γ ⊢ B     
-- ───────────────
-- Γ - {A} ⊢ A → B
introRule :: Formula -> Theorem -> Theorem
introRule a (Theorem gamma b) = Theorem (gamma `Set.difference` Set.singleton a) (ImpF a b)

-- Γ ⊢ A → B  Δ ⊢ A
-- ────────────────
--    Γ ∪ Δ ⊢ B
elimRule :: Theorem -> Theorem -> Maybe Theorem
elimRule (Theorem gamma imp) (Theorem delta a) = case imp of
  VarF _ -> Nothing
  ImpF _ b -> 
    if imp == ImpF a b
      then Just $ Theorem (gamma `Set.union` delta) b
      else Nothing

----------------------------------
-- 2. Goal-directed proof state --
----------------------------------

data Goal = Todo

data GoalState = Todo2

data Tactic = Todo3

by :: Tactic -> GoalState -> GoalState
by = undefined

----------------
-- 3. Tactics --
----------------

assumption :: Tactic
assumption = undefined

introTactic :: Tactic
introTactic = undefined

elimTactic :: Tactic
elimTactic = undefined

-----------------
-- 4. Commands --
-----------------

-- TODO

main :: IO ()
main = main
