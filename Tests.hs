import           Test.QuickCheck (quickCheck)
import           TypeChecker

-- Expected error messages. DON'T CHANGE THESE!
errorIfBranches = "Type error: the two branches of an `if` must have the same type."
errorIfCondition = "Type error: the condition of an `if` must be boolean."
errorCallNotAFunction = "Type error: first expression in a function call must be a function."
errorCallWrongArgNumber = "Type error: function called with the wrong number of arguments."
errorCallWrongArgType = "Type error: function called with an argument of the wrong type."
errorUnboundIdentifier = "Error: unbound identifier."
errorTypeUnification = "Type error: inconsistent set of type constraints generated during type inference."

-- | Sample tests for `If`.
test_IfCorrect =
    runTypeCheck (JustExpr $ If (BoolLiteral True) (IntLiteral 3) (IntLiteral 4)) ==
    Right Int_

test_IfBadCondition =
    runTypeCheck (JustExpr $ If (IntLiteral 10) (IntLiteral 3) (IntLiteral 4)) ==
    Left errorIfCondition

test_IfBadBranches =
    runTypeCheck (JustExpr $ If (BoolLiteral True) (IntLiteral 3) (BoolLiteral False)) ==
    Left errorIfBranches

-- Propagate error upwards.
test_IfSubExprError =
    runTypeCheck (JustExpr $
                    If (BoolLiteral True)
                       (IntLiteral 3)
                       (If (IntLiteral 10) (IntLiteral 3) (IntLiteral 4))) ==
    -- Note that the error comes from the condition `IntLiteral 10` in the inner `If`.
    Left errorIfCondition


-- | Sample tests for `Call`.
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


main :: IO ()
main = do
    quickCheck test_IfCorrect
    quickCheck test_IfBadCondition
    quickCheck test_IfBadBranches
    quickCheck test_IfSubExprError
    quickCheck test_CallCorrect
    quickCheck test_CallNotAFunction
    quickCheck test_CallWrongArgNumber
    quickCheck test_CallWrongArgType
    quickCheck test_DefineOne
    quickCheck test_DefineTwo
