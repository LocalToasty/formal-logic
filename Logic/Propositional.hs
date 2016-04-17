module Logic.Propositional
( Proposition(Val, Var, Not, And, Or)
, (&), (<|>), (-->), (<->), (</>)
, eval
, equiv
, depth
, varNames
, satisfiable, satisfying, tautology
, dnf
) where

import Data.List (union)

-- | Data type for propositions.
data Proposition
  = Val Bool                     -- ^ boolean value
  | Var String                   -- ^ boolean variable
  | Not Proposition              -- ^ negation
  | And Proposition Proposition  -- ^ conjunction
  | Or  Proposition Proposition  -- ^ disjunction
  deriving (Eq)

instance Show Proposition where
  -- | Converts a proposition into a readable string.
  show (Not p)     = "!" ++ show p
  show (p `And` q) = lhs ++ " & " ++ rhs
    where lhs = case p of
                  (Or _ _) -> "(" ++ show p ++ ")"
                  _        -> show p
          rhs = case q of
                  (Or _ _) -> "(" ++ show q ++ ")"
                  _        -> show q
  show (p `Or` q) = lhs ++ " | " ++ rhs
    where lhs = case p of
                  (And _ _) -> "(" ++ show p ++ ")"
                  _         -> show p
          rhs = case q of
                  (And _ _) -> "(" ++ show q ++ ")"
                  _         -> show q
  show (Val False) = "0"
  show (Val True)  = "1"
  show (Var name)  = name

-- Helper functions to make construction of propositions easier
(&) = And                               -- ^ and
(<|>) = Or                              -- ^ or
p --> q = Not p `Or` q                  -- ^ implies
p <-> q = (p --> q) & (q --> p)         -- ^ equivalent
p </> q = (p & Not q) `Or` (Not p & q)  -- ^ xor

-- | An interpretation is a mapping from variables to boolean values.
type Interpretation = [(String,Bool)]

-- | Evaluates a proposition.
-- If the given interpretation isn't fitting, Nothing is returned.
eval :: Proposition -> Interpretation -> Maybe Bool
eval (Val v)     vars = Just v
eval (Var name)  vars = lookup name vars
eval (Not p)     vars = not <$> eval p vars
eval (p `And` q) vars = (&&) <$> eval p vars <*> eval q vars
eval (p `Or` q)  vars = (||) <$> eval p vars <*> eval q vars

-- | Checks if two propositions are equivalent.
equiv :: Proposition -> Proposition -> Bool
equiv p q = all (\x -> eval p x == eval q x) $ interps $ p & q

-- | Determines the depth of a proposition.
-- Atomic propositions (i.e. values, variables) are considered to have a
-- depth of 0.  Every junctor adds 1 to the maximum level of its
-- subpropositions.
depth :: Proposition -> Int
depth (Val _)     = 0
depth (Var _)     = 0
depth (Not p)     = depth p + 1
depth (p `And` q) = max (depth p) (depth q) + 1
depth (p `Or` q)  = max (depth p) (depth q) + 1

-- | Determines the variables in a proposition.
varNames :: Proposition -> [String]
varNames (Var name)  = [name]
varNames (Not p)     = varNames p
varNames (p `And` q) = (varNames p) `union` (varNames q)
varNames (p `Or` q)  = (varNames p) `union` (varNames q)
varNames _           = []

-- | Checks if a proposition is satisfiable.
satisfiable :: Proposition -> Bool
satisfiable p = any ((== Just True) . eval p) $ interps p

-- | Generates all sarisfying interpretations for a proposition.
satisfying :: Proposition -> [Interpretation]
satisfying p = filter ((== Just True) . eval p) $ interps p

-- | Checks if a proposition is a tautology.
tautology :: Proposition -> Bool
tautology p = all ((Just True ==) . eval p) $ interps p

-- | Generates all fitting interpretations.
interps :: Proposition -> [Interpretation]
interps p = map (zip vars) $ boolLists $ length vars
  where vars = varNames p

-- | Generates all possible lists of n booleans.
boolLists :: Int -> [[Bool]]
boolLists 0 = []
boolLists 1 = [[False],[True]]
boolLists n = (map (False:) prev) ++ (map (True:) prev)
  where prev = boolLists $ n - 1

-- | Converts a interpretation into a conjunctive term.
conjunction :: Interpretation -> Proposition
conjunction i = case literals of
                  []   -> Val False
                  p:ps -> foldl And p ps
  where literals = map toTerm i
        toTerm (name,True)  = Var name
        toTerm (name,False) = Not $ Var name

-- | Converts a proposition into its disjunctive normal form.
dnf :: Proposition -> Proposition
dnf p = case terms of
          []   -> Val False
          q:qs -> foldl Or q qs
  where terms = map conjunction $ satisfying p
