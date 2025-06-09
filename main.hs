module Main where

import Data.List (find, intercalate)
import Data.Maybe (listToMaybe)
import Data.Set (Set)
import System.IO (hFlush, stdout)
import Text.Read (readMaybe)

import qualified Data.Set as Set

-- A simple LCF-style theorem prover in Haskell.

------------------------
-- 1. Inference rules --
------------------------

data Formula
  = Var !String           -- x₁, x₂, ...
  | Imp !Formula !Formula -- A → B
  deriving (Eq, Ord, Read)

instance Show Formula where
  show (Var x) = x
  show (Imp a b) = "(" ++ show a ++ " → " ++ show b ++ ")"

data Theorem
  = Theorem !(Set Formula) !Formula -- Γ ⊢ A
  deriving (Eq, Ord, Read)

instance Show Theorem where
  show (Theorem gamma a) =
    let gammaStr = if Set.null gamma then "" else intercalate "\n" (map show $ Set.toList gamma) ++ "\n"
    in gammaStr ++ "______________________________________Goal\n" ++ show a

--
-- ─────
-- A ⊢ A
assume :: Formula -> Theorem
assume a = Theorem (Set.singleton a) a

--      Γ ⊢ B     
-- ───────────────
-- Γ - {A} ⊢ A → B
introRule :: Formula -> Theorem -> Theorem
introRule a (Theorem gamma b) = Theorem (gamma `Set.difference` Set.singleton a) (Imp a b)

-- Γ ⊢ A → B  Δ ⊢ A
-- ────────────────
--    Γ ∪ Δ ⊢ B
elimRule :: Theorem -> Theorem -> Maybe Theorem
elimRule (Theorem gamma imp) (Theorem delta a) = case imp of
  Var _ -> Nothing
  Imp _ b ->
    if imp == Imp a b
      then Just $ Theorem (gamma `Set.union` delta) b
      else Nothing

----------------------------------
-- 2. Goal-directed proof state --
----------------------------------

type Justification = [Theorem] -> Maybe Theorem
type Tactic = Goal -> Maybe GoalState

newtype Goal = Goal Theorem
  deriving (Eq, Ord, Read)

instance Show Goal where
  show (Goal thm) = show thm

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
introTactic (Goal (Theorem gamma (Var _))) = Nothing
introTactic (Goal (Theorem gamma (Imp a b))) = do
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
  let imp = Imp assm a -- A → B
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
type Result a = Either String a

-- Get the current goal state, if it exists.
currentState :: History -> Result GoalState
currentState hist = case hist of
  [] -> Left "No current goal state."
  (x:_) -> Right x

-- Set the current goal.
g :: History -> Formula -> Result History
g hist form = do
  let goal = Goal $ Theorem Set.empty form
  return [GoalState { goals = [goal], justification = listToMaybe }]

top :: History -> Result (Theorem, History)
top hist = do
  goalState <- currentState hist
  case justification goalState [] of
    Nothing -> Left "Theorem not yet proven."
    Just thm -> Right (thm, hist)

-- Return the current goal.
p :: History -> Result (Goal, History)
p hist = do
  goalState <- currentState hist
  case listToMaybe $ goals goalState of
    Nothing -> Left "QED."
    Just goal -> Right (goal, hist)

-- Apply a tactic to the current goal.
e :: History -> Tactic -> Result History
e hist tac = do
  curState <- currentState hist
  case by tac curState of
    Nothing -> Left "Failed to apply tactic."
    Just newState -> Right (newState : hist)

-- Undo the last tactic.
b :: History -> Result History
b hist = do
  case hist of
    (_ : oldHist) -> Right oldHist
    [] -> Left "No previous goal state to revert to."

------------------------------
-- 5. Interactive interface --
------------------------------

splitFirst :: String -> (String, String)
splitFirst str = case words str of
  [] -> ("", "")
  (x:xs) -> (x, unwords xs)

main :: IO ()
main = do
  putStrLn "LCF-style theorem prover"
  putStrLn "Type 'help' for a list of commands."
  loop [] -- The empty list denotes the initial history (which is empty)

  where
    loop :: History -> IO ()
    loop hist = do
      putStr "> " >> hFlush stdout
      input <- getLine

      case splitFirst input of
        ("help", rest) -> handleHelpCommand hist rest
        ("top", rest) -> handleTopCommand hist rest
        ("g", rest) -> handleGCommand hist rest
        ("p", rest) -> handlePCommand hist rest
        ("e", rest) -> handleECommand hist rest
        ("b", rest) -> handleBCommand hist rest

        -- Catch-all for unknown commands.
        (cmd, rest) -> putStrLn ("Unknown command '" <> cmd <> "'. Type 'help' for a list of commands.") >> loop hist

    handleHelpCommand hist input = case input of
      "" -> do
        putStrLn "Available commands:"
        putStrLn "  g <formula>  Set the current goal to the given formula."
        putStrLn "  p            Print the current goal."
        putStrLn "  e <tactic>   Apply a tactic to the current goal."
        putStrLn "  b            Undo the last tactic."
        putStrLn "  top          Show the proven theorem."
        putStrLn "  help         Show this help message."
        putStrLn ""
        putStrLn "<tactic>  ::= 'intro' | 'elim' , <formula> | 'assumption' ;"
        putStrLn "<formula> ::= 'Var' , <string> | 'Imp' , <formula> , <formula> | '(' , <formula> , ')' ;"
        putStrLn "<string>  ::= '\"' , ? any sequence of characters ? , '\"' ;"
        loop hist
      _ -> putStrLn "Unexpected input for 'help' command. Usage: 'help'" >> loop hist

    handleTopCommand hist input = case top hist of
      Left err -> putStrLn err >> loop hist
      Right (thm, newHist) -> do
        print thm
        loop newHist

    handleGCommand hist input = case readMaybe input :: Maybe Formula of
      Nothing -> putStrLn "Invalid formula." >> loop hist
      Just form -> case g hist form of
        Left err -> putStrLn err >> loop hist
        Right newHist -> handlePCommand newHist "" >> loop newHist

    handlePCommand hist "" = case p hist of
      Left err -> putStrLn err >> loop hist
      Right (goal, newHist) -> do
        print goal
        loop newHist

    handlePCommand hist _input = putStrLn "Unexpected input for 'p' command. Usage: 'p'" >> loop hist

    handleECommand hist input = case tacticFun of
      Nothing -> putStrLn "Invalid tactic." >> loop hist
      Just tacticFun -> case e hist tacticFun of
        Left err -> putStrLn err >> loop hist
        Right newHist -> handlePCommand newHist "" >> loop newHist

      where
        tacticFun = case splitFirst input of
          ("intro", rest) -> return introTactic
          ("elim", rest) -> do
            form <- readMaybe rest :: Maybe Formula
            return $ elimTactic form
          ("assumption", _) -> return assumption
          _input -> Nothing

    handleBCommand hist "" = case b hist of
      Left err -> putStrLn err >> loop hist
      Right newHist -> handlePCommand newHist "" >> loop newHist

    handleBCommand hist _input = putStrLn "Unexpected input for 'b' command. Usage: 'b'" >> loop hist