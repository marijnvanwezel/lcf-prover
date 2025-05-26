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
by tactic curState = case goals curState of
  -- No goals left to prove.
  [] -> Nothing
  (goal:rest) -> do
    -- Apply the tactic to the top goal.
    newState <- tactic goal

    -- The new goals are the goals returned by the tactic, and the remaining goals.
    let combinedGoals = goals newState ++ rest
    
    -- The new justification first applies the new justification to the new goals, and then the old
    -- justification to the result of the new justification and the remaining goals.
    -- FIXME (2025-05-26): Perhaps we can simply use [goals newState] and [goals curState] instead of the splitAt?
    let combinedJustification thms = let (topGoals, remainingGoals) = splitAt (length $ goals newState) thms in
                                         justification curState (justification newState topGoals : remainingGoals)
    
    return $ GoalState 
      { goals = combinedGoals
      , justification = combinedJustification
      }

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
