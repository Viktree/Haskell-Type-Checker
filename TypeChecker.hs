{- CSC324 Winter 2018: Assignment 2

*Before starting, please review the general assignment guidelines at
https://www.cs.toronto.edu/~david/csc324/homework.html*

Note: See the Exercise 9 starter code for some additional introductory comments.
We omitted them here so that we could draw your attention to the new parts not
found on the exercise.
-}

-- The module definition line, including exports. Don't change this!
module TypeChecker (runTypeCheck,
                    Prog(..),
                    Expr(..),
                    Type(..),
                    TypeCheckResult) where

import qualified Data.Map.Strict as Map
import qualified Data.Set        as Set
-- The following are imported for your convenience. You may or may not
-- find these useful (consult the relevant documentation); if you don't
-- use them, please remove them.
import qualified Data.Either     as Either
import qualified Data.List       as List
import qualified Data.Maybe      as Maybe

-------------------------------------------------------------------------------

-- |
-- = Data types
--

data Prog
    = JustExpr Expr
    | WithDefines [(String, Expr)] Expr
    deriving Show

data Expr = IntLiteral Int
          | BoolLiteral Bool
          | Identifier String
          | If Expr Expr Expr
          | Call Expr [Expr]
          -- NEW (not on Exercise 9). The first argument is a list of parameter names,
          -- and the second argument is a body expression.
          | Lambda [String] Expr
          deriving (Show, Eq)

data Type
    = Bool_
    | Int_
    | Function [Type] Type
    | TypeVar String
    deriving (Show, Eq, Ord)

-- | Helper for generating type variables for function parameters.
nameToTypeVar :: String -> Type
nameToTypeVar label = TypeVar $ "tvar_" ++ label

-- Helper function:
-- 'Convert' Eithers into Maybes
transformEitherMaybe :: Either a b -> Maybe b
transformEitherMaybe (Left  _)   = Nothing
transformEitherMaybe (Right val) = Just val

-- Helper function:
-- Collect the Maybe to outside a list, from Lab 10
collectM :: Monad m => [m a] -> m [a]
collectM = foldr
    (\ maybeVal maybeAcc -> do
       val <- maybeVal
       acc <- maybeAcc
       return $ val : acc)
    (return [])

-- Helper function:
-- Checks if given Type is a TypeVar
isTypeVar :: Type -> Bool
isTypeVar (TypeVar _) = True
isTypeVar _           = False

-- Helper function
-- Accumulate a list of ConstraintMaps into one ConstraintMap
filterDefiniteConstraints :: (Foldable t) => t (Maybe ConstraintMap) -> ConstraintMap
filterDefiniteConstraints = foldl
    (\acc m -> case m of
        Just c -> Map.union acc c
        _      -> acc)
    Map.empty

type TypeEnv = Map.Map String Type

builtins :: TypeEnv
builtins = Map.fromList
    [ ("+", Function [Int_, Int_] Int_)
    , ("-", Function [Int_, Int_] Int_)
    , ("*", Function [Int_, Int_] Int_)
    , ("quotient", Function [Int_, Int_] Int_)
    , ("remainder", Function [Int_, Int_] Int_)

    , ("<", Function [Int_, Int_] Bool_)

    , ("and", Function [Bool_, Bool_] Bool_)
    , ("or", Function [Bool_, Bool_] Bool_)
    , ("not", Function [Bool_] Bool_)

    -- NEW: built-in polymorphic functions. The type parameters here are given unique
    -- names; see handout for discussion of name collisions among type parameters.
    , ("return-zero", Function [TypeVar "t1"] Int_)
    , ("identity", Function [TypeVar "t2"] (TypeVar "t2"))
    , ("apply", Function [Function [TypeVar "t3"] (TypeVar "t4"), TypeVar "t3"] (TypeVar "t4"))
    , ("return-it", Function [TypeVar "t5"] (Function [TypeVar "t6"] (TypeVar "t5")))
    ]


type TypeCheckResult = Either String Type

{-
The new TypeCheckResult' type for Task2
This format allows for propagating constraints throughout the program.
-}
type TCR2 = Either String (Type, Map.Map Type Type)

-- Expected error messages. DON'T CHANGE THESE!
errorIfBranches = "Type error: the two branches of an `if` must have the same type."
errorIfCondition = "Type error: the condition of an `if` must be boolean."
errorCallNotAFunction = "Type error: first expression in a function call must be a function."
errorCallWrongArgNumber = "Type error: function called with the wrong number of arguments."
errorCallWrongArgType = "Type error: function called with an argument of the wrong type."
errorUnboundIdentifier = "Error: unbound identifier."
errorTypeUnification = "Type error: inconsistent set of type constraints generated during type inference."


-------------------------------------------------------------------------------
-- | Entry point to the type-checking. We've implemented this for you (though you will
-- probably need to change over the course of the assignment).
runTypeCheck :: Prog -> TypeCheckResult
runTypeCheck (JustExpr expr) = case typeCheck builtins expr of
    Left err  -> Left err
    Right ret -> Right (fst ret)
-- Modified here to handle Task2
runTypeCheck (WithDefines definitions expr) =
    case buildTypeEnv builtins definitions of
        Left msg     -> Left msg
        Right newConstraints -> case typeCheck newConstraints expr of
            Left err  -> Left err
            Right ret -> Right (fst ret)


-- | The "core" type-checking function.
typeCheck :: TypeEnv -> Expr -> TCR2
typeCheck _ (IntLiteral _) = Right (Int_, Map.empty)
typeCheck _ (BoolLiteral _) = Right (Bool_, Map.empty)
typeCheck env (Identifier s) =
    case Map.lookup s env of
        Nothing -> Left errorUnboundIdentifier
        Just t  -> Right (t, Map.empty)

-- Handle If
typeCheck env (If c t e) = do
    (ifType, _) <- typeCheck env c
    (rawFirstType, fcons)  <- typeCheck env t
    (rawSecondType, scons) <- typeCheck env e
    -- Collect constraints
    let newEntries = Map.fromList [(rawFirstType, rawSecondType), (ifType, Bool_)]
        newConstraints = Map.unions [scons, fcons, newEntries]
        resolvedFirstType = resolve newConstraints rawFirstType
        resolvedSecondType = resolve newConstraints rawSecondType
    -- Check that if returns a boolean and that the branches are same type
    if ifType == Bool_ || isTypeVar ifType
    then if resolvedFirstType == resolvedSecondType
        then Right (resolvedFirstType, newConstraints)
        else Left errorIfBranches
    else Left errorIfCondition

-- Handle Call
typeCheck env (Call f@(Identifier _) args) = do
    (Function reqArgs functionReturn, _) <- typeCheck env f
    -- Check that the arguments and parameters are of same length
    if length args == length reqArgs
    then let
        -- Check that arguments and parameters are of same type
        argType = let
            checkArgs y = typeCheck env y >>= (\(t, _) -> return t)
            in map (transformEitherMaybe . checkArgs) args
        -- Collect constraints
        newConstraints = let
            constraintsFromArgs = map
                (\x -> transformEitherMaybe $ typeCheck env x >>= (\(_, s) -> return s))
                args
            otherConstraints = map
                (\(p, ma) -> ma >>= unify p >>= consolidate)
                (zip reqArgs argType)
            in Map.union  -- Join the constraints together
                (filterDefiniteConstraints constraintsFromArgs)
                (filterDefiniteConstraints otherConstraints)
        -- Resolve argument and parameter types using above constraints
        resolvedArgTypes = collectM argType >>= Just . map (resolve newConstraints)
        resolved  = map (resolve newConstraints) reqArgs
        -- Check that the resolved argument and parameter types match
        in if Just resolved == resolvedArgTypes
            then case functionReturn of
                p@(TypeVar _) ->
                    case Map.lookup p newConstraints of
                        Just val -> Right (val, newConstraints)
                        Nothing  -> Left errorUnboundIdentifier
                _ -> Right (functionReturn, newConstraints)
            else Left errorCallWrongArgType
    else Left errorCallWrongArgNumber

-- Handle Call Error
typeCheck _ (Call _ _) = Left errorCallNotAFunction

-- Handle Lambda
typeCheck env (Lambda names body) = do
    -- Make an environment with 'fresh variables'
    let argTypes = [nameToTypeVar x | x <- names]
        tempEnv = Map.union env $ Map.fromList $ zip names argTypes
    -- Typecheck the body with the environment with fresh variables
    (retType, newConstraints)  <- typeCheck tempEnv body
    let resolvedArgs = map (resolve newConstraints) argTypes
        resolvedRet = resolve newConstraints retType
    Right (Function resolvedArgs resolvedRet, newConstraints)

buildTypeEnv :: TypeEnv -> [(String, Expr)] -> Either String TypeEnv
buildTypeEnv env = foldl buildTypeEnvHelper (Right env)

buildTypeEnvHelper :: Either String TypeEnv -> (String, Expr) -> Either String TypeEnv
buildTypeEnvHelper safeEnv (val, valType) = do
    env <- safeEnv
    (valTypeEvaluated, _) <- typeCheck env valType
    Right (Map.insert val valTypeEvaluated env)


-------------------------------------------------------------------------------

{- |
== Type Unification
This section contains more information about the implementation of
type unification required to handle polymorphic types.

This section is organized into four parts:
  - The type definitions.
  - The function `unify` for generating type constraints.
  - The function `consolidate` for taking a set of constraints and processing them,
    including looking for errors.
  - The function `resolve`, used to take a type variable and determine what type
    it should take on, given some type constraints.

The three functions can be used to type-check generic function calls in the following way
(given in pseudocode):
  1. Check that the number of arguments matches the number of params of the function.
  2. `unify` each argument type with its corresponding parameter type, and accumulate constraints.
  3. `consolidate` all constraints (checks for errors).
  4. `resolve` the return type using the consolidated constraints.

As we've discussed in the handout, you may freely change the given types and bits of
implementation provided; just make sure you document your work carefully.
-}

-- | This is a type synonym. The tuple represents an *equivalence* between
-- two types; for example, "a is an Int" is represented as (TypeVar "a", Int_).
-- Recommended invariant: the first type is always a type variable.
-- It'll be up to you to enforce this; the compiler won't catch it!
type TypeConstraint = (Type, Type)
-- | A set of type constraints. Used to accumulate multiple constraints.
type TypeConstraints = Set.Set TypeConstraint

{-
The renamed and modified type for Consolidate.
This is a Map of types mainly to handle and help easily resolve what types
TypeVars are supposed to be.
For example, fromList [(TypeVar "t1", Int_)] means that TypeVar t1 should
later be resolved to be of type Int_.
-}
type ConstraintMap = Map.Map Type Type


-- | This is the main unification function.
-- It takes two types (possibly type variables) and succeeds if the types unify,
-- and fails otherwise.
--
-- Formally, we say two types t1 and t2 *unify* if:
--   - t1 or t2 is a type variable.
--       In this case, return a single type constraint (t1, t2).
--   - t1 and t2 are the same primitive type (Int_ or Bool_).
--       In this case, return no type constraints.
--   - t1 and t2 are both function types that take the same number of parameters,
--     *and* their corresponding parameter types unify, *and* their return types unify.
--       In this case, return all the type constraints from unifying the parameters
--       and return types.
unify :: Type -> Type -> Maybe TypeConstraints
unify t1@(TypeVar _) t2 = Just (Set.fromList [(t1, t2)])
unify t1 t2@(TypeVar _) = Just (Set.fromList [(t2, t1)])
unify Int_ Int_ = Just Set.empty
unify Bool_ Bool_ = Just Set.empty
unify (Function p1 r1) (Function p2 r2) =
  -- Check parameters of equal length, unify their types
  if length p1 == length p2
    then foldl (\acc (x,y) -> do
      u <- unify x y
      a <- acc
      Just (Set.union a u))
      (Just Set.empty) (zip (r1:p1) (r2:p2))
    else Nothing
unify _ _ = Nothing

-- | Takes the generated constraints and processs them.
-- Returns `Nothing` if the constraints cannot be satisfied (this is a type error).
-- The returned value is ConstraintMap to make passing constraints along easier
-- for resolving types later on in prog.
-- Sets have a powerful no-duplicates property which we use here.
consolidate :: TypeConstraints -> Maybe ConstraintMap
consolidate constraints =
  let constraintTypeVars = map fst (Set.toList constraints)
  in
    -- If converting to set changes the length, we lost conflicting constraints
    if Set.toList (Set.fromList constraintTypeVars) == constraintTypeVars
    then Just (Map.fromList (Set.toList constraints))
    else Nothing

-- | Takes the consolidated constraints and a type, and returns a
-- new type obtained by replacing any type variables in the input type
-- based on the given constraints.
-- Note: if there are no constraints on a type variable, you should
-- simply return the type variable (it remains generic).
resolve :: ConstraintMap -> Type -> Type
resolve _ Int_                              = Int_
resolve _ Bool_                             = Bool_
resolve constraints t@(TypeVar _)           =
  -- Lookup and recursively resolve if needed, return type based on constraints
  case Map.lookup t constraints of
    Just newT@(TypeVar _) -> resolve constraints newT -- matched another TypeVar
    Just ret              -> ret  -- matched some other type
    Nothing               -> t  -- no constraints, generic

-- Don't forget about this case: the function type might contain
-- type variables.
-- Resolves the params and return type accordingly
resolve constraints (Function params rType) =
  Function (map (resolve constraints) params) (resolve constraints rType)
