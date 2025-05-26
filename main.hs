module Main where

import Data.Set (Set)

import qualified Data.Set as Set
import Data.List (find)
import Data.Maybe (listToMaybe)

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

type Justification = [Theorem] -> Maybe Theorem
type Tactic = Goal -> Maybe GoalState

newtype Goal = Goal Theorem
  deriving (Eq, Ord)

data GoalState
  = GoalState
  { goals :: ![Goal]
  , justification :: !Justification
  }

proves :: Theorem -> Formula -> Bool
proves (Theorem _ a) b = a == b

-- Applies the given tactic to the first goal in the goal state.
by :: Tactic -> GoalState -> Maybe GoalState
by tactic curState = case goals curState of
  -- No goals left to prove.
  [] -> Nothing
  (goal:rest) -> do
    newState <- tactic goal

    return $ GoalState
      { goals = goals newState ++ rest
      , justification = combineJustification newState
      }

  where
    -- The new justification first applies the new justification to the new goals, and then the old
    -- justification to the result of the new justification and the remaining goals.
    -- FIXME (2025-05-26): Perhaps we can simply use [goals newState] and [goals curState] instead of the splitAt?
    combineJustification newState thms = do
      let (topGoals, remainingGoals) = splitAt (length $ goals newState) thms
      thm <- justification newState topGoals
      justification curState (thm : remainingGoals)

----------------
-- 3. Tactics --
----------------

assumption :: Tactic
assumption (Goal (Theorem gamma a))
  | Set.member a gamma = Just $ GoalState
      { goals = []
      , justification = \_ -> return $ assume a
      }
  | otherwise = Nothing

introTactic :: Tactic
introTactic (Goal (Theorem gamma (VarF _))) = Nothing
introTactic (Goal (Theorem gamma (ImpF a b))) = do
  let newGamma = Set.insert a gamma
  let subGoals = [Goal (Theorem newGamma b)]

  return $ GoalState
    { goals = subGoals
    , justification = justification'
    }

  where
    justification' thms = do
      thm <- find (`proves` b) thms
      return $ introRule a thm

elimTactic :: Formula -> Tactic
elimTactic assm (Goal (Theorem gamma a)) = do
  let imp = ImpF assm a -- A → B
  let impThm = Theorem gamma imp -- Γ ⊢ A → B
  let assmThm = Theorem gamma assm -- Γ ⊢ A

  return $ GoalState
    { goals = [Goal impThm, Goal assmThm]
    , justification = justification' imp assm
    }

  where
    justification' imp assm thms = do
      impThm <- find (`proves` imp) thms
      assmThm <- find (`proves` assm) thms
      elimRule impThm assmThm

-----------------
-- 4. Commands --
-----------------

type History = [GoalState]

-- Get the current goal state, if it exists.
currentState :: History -> Maybe GoalState
currentState = listToMaybe

-- Set the current goal.
g :: History -> Formula -> Maybe (Goal, History)
g hist form = do
  let goal = Goal $ Theorem Set.empty form
  case currentState hist of
    Nothing -> return (goal, [GoalState { goals = [goal], justification = listToMaybe }])
    Just goalState ->
      let newState = GoalState
            { goals = goal : goals goalState
            , justification = justification goalState
            }
      in return (goal, newState : hist)

-- Return the current goal.
p :: History -> Maybe (Goal, History)
p hist = do
  goalState <- currentState hist
  goal <- listToMaybe $ goals goalState
  return (goal, hist)

-- Apply a tactic to the current goal.
e :: History -> Tactic -> Maybe (Goal, History)
e hist tac = do
  curState <- currentState hist
  newState <- by tac curState
  p (newState : hist)

-- Undo the last tactic.
b :: History -> Maybe (Goal, History)
b hist = do
  case hist of
    (_ : oldHist) -> p oldHist
    [] -> p hist

main :: IO ()
main = undefined
