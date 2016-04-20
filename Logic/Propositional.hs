module Logic.Propositional
( Proposition(Val, Var, Not, And, Or)
, (&), (<|>), (-->), (<->), (</>)
, eval
, equiv
, depth
, varNames
, satisfiable, satisfying, tautology
, dnf, cnf
) where

import Data.List (union)
import Data.Maybe (fromJust)

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
  show (Val False)         = "0"
  show (Val True)          = "1"
  show (Var name)          = name
  show (Not p@(_ `And` _)) = "!(" ++ show p ++ ")"
  show (Not p@(_ `Or` _))  = "!(" ++ show p ++ ")"
  show (Not p)     = "!" ++ show p
  show (p `And` q) = decorate p ++ " & " ++ decorate q
    where decorate p = case p of
                         (Or _ _) -> "(" ++ show p ++ ")"
                         _        -> show p
  show (p `Or` q) = decorate p ++ " | " ++ decorate q
    where decorate p = case p of
                         (And _ _) -> "(" ++ show p ++ ")"
                         _         -> show p

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

-- | Replaces all occurrences of a variable with a boolean value.
apply :: Proposition -> (String,Bool) -> Proposition
apply p@(Var name) (var,val) | name == var = Val val
                             | otherwise   = p
apply (Not p)      var = Not $ p ! var
apply (p `And` q)  var = (p ! var) & (q ! var)
apply (p `Or` q)   var = (p ! var) <|> (q ! var)
apply p            _   = p

(!) = apply

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
satisfiable p | varNames p == [] = fromJust $ eval p []
              | otherwise        = any ((== Just True) . eval p) $ interps p

-- | Generates all sarisfying interpretations for a proposition.
satisfying :: Proposition -> [Interpretation]
satisfying p = filter ((== Just True) . eval p) $ interps p

-- | Checks if a proposition is a tautology.
tautology :: Proposition -> Bool
tautology p | varNames p == [] = fromJust $ eval p []
            | otherwise        = all ((Just True ==) . eval p) $ interps p

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
-- The conjunctive term evaluates to true for the given interpretation,
-- false otherwise.
conjunction :: Interpretation -> Proposition
conjunction i = case literals of
                  []   -> Val False
                  p:ps -> foldl And p ps
  where literals = map toTerm i
        toTerm (name,True)  = Var name
        toTerm (name,False) = Not $ Var name

disjunction :: Interpretation -> Proposition
disjunction i = case literals of
                  []   -> Val False
                  p:ps -> foldl Or p ps
  where literals = map toTerm i
        toTerm (name,True)  = Not $ Var name
        toTerm (name,False) = Var name

-- | Converts a proposition into its disjunctive normal form.
dnf :: Proposition -> Proposition
dnf p | varNames p == [] = Val $ fromJust $ eval p []
      | otherwise        = case terms of
                             []   -> Val False
                             q:qs -> foldl Or q qs
      where terms = map conjunction $ satisfying p

cnf :: Proposition -> Proposition
cnf p | varNames p == [] = Val $ fromJust $ eval p []
      | otherwise        = case terms of
                             []   -> Val True
                             q:qs -> foldl And q qs
      where terms = map disjunction $ satisfying $ Not p
