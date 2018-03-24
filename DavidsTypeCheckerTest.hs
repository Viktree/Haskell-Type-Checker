{- CSC324 Winter 2018: Assignment 2 Sample tests -}

import Data.Either (isLeft)
import TypeChecker (runTypeCheck,
                    Prog(..),
                    Expr(..),
                    Type(..),
                    TypeCheckResult)
import Test.QuickCheck (quickCheck, label)

errorIfBranches = "Type error: the two branches of an `if` must have the same type."
errorIfCondition = "Type error: the condition of an `if` must be boolean."
errorCallNotAFunction = "Type error: first expression in a function call must be a function."
errorCallWrongArgNumber = "Type error: function called with the wrong number of arguments."
errorCallWrongArgType = "Type error: function called with an argument of the wrong type."
errorUnboundIdentifier = "Error: unbound identifier."
errorTypeUnification = "Type error: inconsistent set of type constraints generated during type inference."


badBranchIf :: Expr
badBranchIf = If (BoolLiteral True) (IntLiteral 3) (BoolLiteral True)


-- Test helper. Produces a label when the test is run.
doTest s test = quickCheck (label s test)

-------------------------------------------------------------------------------
-- | Exercise 9 sample tests
-------------------------------------------------------------------------------
test_IfCorrect =
    runTypeCheck (JustExpr $ If (BoolLiteral True) (IntLiteral 3) (IntLiteral 4)) ==
    Right Int_

test_IfBadCondition =
    runTypeCheck (JustExpr $ If (IntLiteral 10) (IntLiteral 3) (IntLiteral 4)) ==
    Left errorIfCondition

test_IfBadBranches =
    runTypeCheck (JustExpr $ If (BoolLiteral True) (IntLiteral 3) (BoolLiteral False)) ==
    Left errorIfBranches

test_IfSubExprElseError =
    runTypeCheck (JustExpr $
                    If (BoolLiteral True)
                       (IntLiteral 3)
                       (If (IntLiteral 10) (IntLiteral 3) (IntLiteral 4))) ==
    -- Note that the error comes from the condition `IntLiteral 10` in the inner `If`.
    Left errorIfCondition

test_CallCorrect =
    runTypeCheck (JustExpr $
        Call (Identifier "<") [IntLiteral 10, IntLiteral 20]) ==
    Right Bool_

test_CallNotAFunction =
    runTypeCheck (JustExpr $
        Call (BoolLiteral True) [IntLiteral 10, IntLiteral 20]) ==
    Left errorCallNotAFunction

test_CallWrongArgNumber =
    runTypeCheck (JustExpr $
        Call (Identifier "remainder") [IntLiteral 10]) ==
    Left errorCallWrongArgNumber

test_CallWrongArgType =
    runTypeCheck (JustExpr $
        Call (Identifier "or") [BoolLiteral True, IntLiteral 10]) ==
    Left errorCallWrongArgType

test_DefineOne =
    runTypeCheck (WithDefines
        [("x", BoolLiteral True)]
        (Identifier "x")) ==
    Right Bool_

test_DefineTwo =
    runTypeCheck (WithDefines
        [ ("x", IntLiteral 10)
        , ("y", Call (Identifier "<") [Identifier "x", IntLiteral 3])]
        (If (Identifier "y") (Identifier "x") (IntLiteral 3))) ==
    Right Int_


-------------------------------------------------------------------------------
-- | A2 Part 1 sample tests
-------------------------------------------------------------------------------
test_ReturnZero =
    runTypeCheck (JustExpr $
        Call (Identifier "return-zero") [IntLiteral 10]) ==
    Right Int_

test_Id =
    runTypeCheck (JustExpr $
        Call (Identifier "identity") [Identifier "+"]) ==
    Right (Function [Int_, Int_] Int_)

test_IdApply =
    let s = runTypeCheck (JustExpr $
                Call (Identifier "identity") [Identifier "apply"])
    in
        case s of
            -- We don't assume a particular name for the type variables
            -- but do check that it has the same structure as the type of `apply`.
            -- All tests involving with
            Right (Function [Function [TypeVar a] (TypeVar b), TypeVar c] (TypeVar d)) ->
                a == c && b == d && a /= b
            _ -> False

-- Pay attention to the error message here! The problem is considered to be
-- a *bad argument type* error, even though you'll likely detect it through
-- type unification.
test_ApplyWrongArgType =
    runTypeCheck (JustExpr $
        Call (Identifier "apply") [Identifier "not", IntLiteral 4]) ==
    -- Note: this is *also* a wrong arg type error!
    Left errorCallWrongArgType


-------------------------------------------------------------------------------
-- | A2 Part 2 sample tests
-------------------------------------------------------------------------------
test_Lambda =
    runTypeCheck (JustExpr $
        Lambda ["x"] (Call (Identifier "+") [Identifier "x", IntLiteral 3])) ==
    Right (Function [Int_] Int_)

test_LambdaId =
    case runTypeCheck (JustExpr $ Lambda ["x"] (Identifier "x")) of
        Right (Function [TypeVar a] (TypeVar b)) -> a == b
        _ -> False

test_LambdaIf =
    case runTypeCheck (JustExpr $
        Lambda ["x", "y", "z"] (If (Identifier "x") (Identifier "y") (Identifier "z"))) of

        Right (Function [Bool_, TypeVar a, TypeVar b] (TypeVar c)) -> a == b && b == c


-- Note that the type error in the body "propagates up",
-- just like other kinds of expressions.
test_LambdaBodyTypeError =
    runTypeCheck (JustExpr $
        Lambda [] (If (BoolLiteral True) (IntLiteral 3) (BoolLiteral False))) ==
    Left errorIfBranches

-- NOTE: To make the assignment a bit easier, we're accepting *any* error
-- to be reported when an inconsistent set of constraints on a type variable are generated.
-- In the test below, this is indicated through the use of `isLeft` to check the
-- return value, rather than looking for a specific message.
test_LambdaBadUnify =
    isLeft $ runTypeCheck (JustExpr $
        Lambda ["n"]
            (Call (Identifier "and") [
                Call (Identifier "not") [Identifier "n"],              -- n must be a boolean
                Call (Identifier "+") [Identifier "n", IntLiteral 3]   -- n must be an int
            ]))


main :: IO ()
main = do
    doTest "simple If (sample test)" test_IfCorrect
    doTest "If with non-boolean condition (sample test)" test_IfBadCondition
    doTest "If with non-matching branch types (sample test)" test_IfBadBranches
    doTest "If where the 'else' branch has a type error (sample test)" test_IfSubExprElseError
    doTest "Correct function call (sample test)" test_CallCorrect
    doTest "Function call where function expression doesn't have a function type (sample test)" test_CallNotAFunction
    doTest "Function call with the wrong number of arguments (sample test)" test_CallWrongArgNumber
    doTest "Function call where an argument has the wrong type (sample test)" test_CallWrongArgType
    doTest "Single definition (sample test)" test_DefineOne
    doTest "Two definitions (sample test)" test_DefineTwo

    doTest "return-zero: primitive type (sample test)" test_ReturnZero
    doTest "identity: monomorphic (non-polymorphic) function type (sample test)" test_Id
    doTest "identity: polymorphic function type (apply) (sample test)" test_IdApply
    doTest "apply: called with a second argument that's incompatible with the first (sample test)" test_ApplyWrongArgType

    doTest "lambda: basic type inference (sample test)" test_Lambda
    doTest "lambda: type inference for the identity function (\\x -> x)" test_LambdaId
    doTest "lambda: type inference for an If expression (sample test)" test_LambdaIf
    doTest "lambda: type-check error in body of function (sample test)" test_LambdaBodyTypeError
    doTest "lambda: a simple type inference error (sample test)" test_LambdaBadUnify
