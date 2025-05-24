module Main where

import Data.Set (Set)

import qualified Data.Set as Set

data Error = EliminationError

------------------------
-- 1. Inference rules --
------------------------

data Formula
  = VarF !Int              -- x₁, x₂, ...
  | ImpF !Formula !Formula -- A → B
  deriving (Eq, Ord)

data Theorem
  = Theorem !(Set Formula) !Formula -- Γ ⊢ A
  deriving (Eq, Ord)

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

type Justification = [Theorem] -> Theorem
type Tactic = Goal -> Maybe GoalState

newtype Goal = Goal Theorem
  deriving (Eq, Ord)

data GoalState 
  = GoalState
  { goals :: ![Goal]
  , justification :: !Justification
  }

-- Applies the given tactic to the first goal in the goal state.
by :: Tactic -> GoalState -> Maybe GoalState
-- "No more goals."
by tactic state = case goals state of
  [] -> Nothing
  (g:gs) -> do
    state' <- tactic g
    
    undefined --TODO

----------------
-- 3. Tactics --
----------------

assumption :: Tactic
assumption (Goal (Theorem gamma a))
  | Set.member a gamma = Just $ GoalState 
      { goals = []
      , justification = \_ -> assume a
      }
  | otherwise = Nothing

introTactic :: Tactic
introTactic (Goal (Theorem gamma (VarF _))) = Nothing
introTactic (Goal (Theorem gamma (ImpF a b))) = do
  let gamma' = Set.insert a gamma
  Just $ GoalState 
    { goals = [Goal (Theorem gamma' b)]
    , justification = undefined -- TODO
    }

elimTactic :: Formula -> Tactic
elimTactic = undefined

-----------------
-- 4. Commands --
-----------------

-- TODO

main :: IO ()
main = main
