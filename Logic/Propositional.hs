module Logic.Propositional
( Proposition(Val, X, Not, And, Or)
, (&), (<|>), (-->), (<->), (</>)
, eval
, equiv
, depth
, vars
, satisfiable, satisfying, tautology
, dnf
) where

-- | Data type for propositions.
data Proposition
  = Val Bool                     -- ^ boolean value
  | X   Int                      -- ^ boolean variable
  | Not Proposition              -- ^ negation
  | And Proposition Proposition  -- ^ conjunction
  | Or  Proposition Proposition  -- ^ disjunction
  deriving (Eq)

instance Show Proposition where
  -- | Converts a proposition into a readable string.
  show (Val False)    = "0"
  show (Val True)     = "1"
  show (X i)          = "X" ++ show i
  show (Not p)        = "!" ++ show p
  show (p `And` q)    = "(" ++ show p ++ " & " ++ show q ++ ")"
  show (p `Or` q)     = "(" ++ show p ++ " | " ++ show q ++ ")"

-- Helper functions to make construction of propositions easier
(&) = And                               -- ^ and
(<|>) = Or                              -- ^ or
p --> q = Not p `Or` q                  -- ^ implies
p <-> q = (p --> q) & (q --> p)         -- ^ equivalent
p </> q = (p & Not q) `Or` (Not p & q)  -- ^ xor

-- | Evaluates a proposition.
eval :: Proposition -> [Bool] -> Bool
eval (Val v)      xs = v
eval (X i)        xs = xs !! i
eval (Not p)      xs = not $ eval p xs
eval (p `And` q)  xs = eval p xs && eval q xs
eval (p `Or` q)   xs = eval p xs || eval q xs

-- | Checks if two propositions are equivalent.
equiv :: Proposition -> Proposition -> Bool
equiv p q = all (\x -> eval p x == eval q x) interps
  where interps = interp $ max (vars p) (vars q)

-- | Determines the depth of a proposition.
-- Atomic propositions (i.e. values, variables) are considered to have a
-- depth of 0.  Every junctor adds 1 to the maximum level of its
-- subpropositions.
depth :: Proposition -> Int
depth (Val _)     = 0
depth (X _)       = 0
depth (Not p)     = depth p + 1
depth (p `And` q) = max (depth p) (depth q) + 1
depth (p `Or` q)  = max (depth p) (depth q) + 1

-- | Determines the number of variables in a proposition.
vars :: Proposition -> Int
vars (X i)        = i + 1
vars (Not  p)     = vars p
vars (p `And` q)  = max (vars p) (vars q)
vars (p `Or` q)   = max (vars p) (vars q)
vars _            = 0

-- | Checks if a proposition is satisfiable.
satisfiable :: Proposition -> Bool
satisfiable p = any (eval p) interps
  where interps = interp $ vars p

-- | Generates all sarisfying interpretations for a proposition.
satisfying :: Proposition -> [[Bool]]
satisfying p = filter (eval p) interps
  where interps = interp $ vars p

-- | Checks if a proposition is a tautology.
tautology :: Proposition -> Bool
tautology p = all (eval p) interps
  where interps = interp $ vars p

-- | Generates all possible interpretations.
interp :: Int -> [[Bool]]
interp 0 = []
interp 1 = [[False],[True]]
interp n = (map (False:) prev) ++ (map (True:) prev)
  where prev = interp $ n - 1

-- | Converts a interpretation into a conjunctive term.
conjunction :: [Bool] -> Proposition
conjunction xs = case literals of
                   []   -> Val False
                   p:ps -> foldl And p ps
  where vars = map X [0..length xs]
        literals = zipWith (\b x -> if b then x else Not x) xs vars

-- | Converts a proposition into its disjunctive normal form.
dnf :: Proposition -> Proposition
dnf p = case terms of
          []   -> Val False
          q:qs -> foldl Or q qs
  where terms = map conjunction $ satisfying p
