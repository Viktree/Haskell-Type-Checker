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
runTypeCheck (JustExpr expr) = typeCheck builtins expr
runTypeCheck (WithDefines definitions expr) =
    case buildTypeEnv builtins definitions of
        Left msg     -> Left msg
        Right newEnv -> typeCheck newEnv expr


-- | The "core" type-checking function.
typeCheck :: TypeEnv -> Expr -> TypeCheckResult
typeCheck _ (IntLiteral _) = Right Int_
typeCheck _ (BoolLiteral _) = Right Bool_
typeCheck env (Identifier s) =
    case Map.lookup s env of
        Nothing -> Left errorUnboundIdentifier
        Just t  -> Right t

typeCheck env (If c t e) = do
    ifType <- typeCheck env c
    if ifType == Bool_
    then do
        firstType  <- typeCheck env t
        secondType <- typeCheck env e
        if firstType == secondType
        then Right firstType
        else Left errorIfBranches
    else Left errorIfCondition

typeCheck env (Call f args) =
    case f of
        Identifier _ -> do
            (Function requiredArgs functionReturn) <- typeCheck env f
            if length args == length requiredArgs
            then
                if map Right requiredArgs == map (typeCheck env) args
                then Right functionReturn
                else Left errorCallWrongArgType
            else Left errorCallWrongArgNumber
        _            -> Left errorCallNotAFunction

typeCheck env (Lambda names body) = undefined

buildTypeEnv :: TypeEnv -> [(String, Expr)] -> Either String TypeEnv
buildTypeEnv env = foldl buildTypeEnvHelper (Right env)

buildTypeEnvHelper :: Either String TypeEnv -> (String, Expr) -> Either String TypeEnv
buildTypeEnvHelper safeEnv (val, valType) = do
    env <- safeEnv
    valTypeEvaluated <- typeCheck env valType
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

-- You should choose a different name representation for this type, or remove it entirely.
type ConsolidatedConstraints = TypeConstraints


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
unify (TypeVar s1) t2 = Just (Set.fromList [(TypeVar s1, t2)])
unify t1 (TypeVar s2) = Just (Set.fromList [(t1, TypeVar s2)])
unify Int_ Int_ = Just Set.empty
unify Bool_ Bool_ = Just Set.empty
unify (Function p1 r1) (Function p2 r2) =
  if length p1 == length p2
    then
      let pPairs = zip p1 p2
          cons = foldl (\acc (x,y) ->
            case unify x y of
              Nothing -> Nothing
              _ -> (unify x y)) (Just Set.empty) pPairs
      in
        case cons of
          Nothing -> Nothing
          _ -> cons
    else Nothing
unify t1 t2 = Nothing
-- both function types
-- same # of params
-- matching params unify
-- returns unify
-- return all constraints


-- | Takes the generated constraints and processs them.
-- Returns `Nothing` if the constraints cannot be satisfied (this is a type error).
-- Note that the returned value will depend on your representation of `ConstraintSets`.
consolidate :: TypeConstraints -> Maybe ConsolidatedConstraints
consolidate constraints = undefined


-- | Takes the consolidated constraints and a type, and returns a
-- new type obtained by replacing any type variables in the input type
-- based on the given constraints.
-- Note: if there are no constraints on a type variable, you should
-- simply return the type variable (it remains generic).
resolve :: ConsolidatedConstraints -> Type -> Type
resolve _ Int_                              = Int_
resolve _ Bool_                             = Bool_
resolve constraints t@(TypeVar _)           = undefined
-- Don't forget about this case: the function type might contain
-- type variables.
resolve constraints (Function params rType) = undefined
