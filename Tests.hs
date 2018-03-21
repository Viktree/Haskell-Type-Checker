import           Test.QuickCheck (quickCheck)
import           TypeChecker
import           Data.Set                       as Set

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

{- unify
- t1 is a TypeVar, t2 is not
- t2 is a TypeVar, t1 is not
- t1 and t2 are Int_
- t1 and t2 are Bool_
- t1 and t2 are Function types
-}
test_UnifyT1TypeVar =
  (unify (TypeVar "a") Int_) == Just (Set.fromList [(TypeVar "a", Int_)])
test_UnifyT2TypeVar =
  (unify Bool_ (TypeVar "b")) == Just (Set.fromList [(Bool_, TypeVar "b")])
test_UnifyPrimitivesInt =
  (unify Int_ Int_) == Just Set.empty
test_UnifyPrimitivesBool =
  (unify Bool_ Bool_) == Just Set.empty
test_UnifyFunctionCanUnifySimple =
  (unify (Function [(TypeVar "a")] Int_) (Function [Int_] Int_)) ==
    Just (Set.fromList [(TypeVar "a", Int_)])
test_UnifyFunctionCanUnifyLonger =
  (unify
    (Function [(TypeVar "a"), (TypeVar "b")] Int_)
    (Function [Int_, Int_] Int_)) ==
    Just (Set.fromList [(TypeVar "a", Int_), (TypeVar "b", Int_)])
test_UnifyFunctionCanUnifyEvenLonger =
  (unify
    (Function [(TypeVar "a"), (TypeVar "b"), (TypeVar "c")] (TypeVar "r"))
    (Function [Int_, Int_, Bool_] Bool_)) ==
    Just (Set.fromList [(TypeVar "r", Bool_), (TypeVar "a", Int_), (TypeVar "b", Int_), (TypeVar "c", Bool_)])

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
    quickCheck test_UnifyT1TypeVar
    quickCheck test_UnifyT2TypeVar
    quickCheck test_UnifyPrimitivesInt
    quickCheck test_UnifyPrimitivesBool
    quickCheck test_UnifyFunctionCanUnifySimple
    quickCheck test_UnifyFunctionCanUnifyLonger
    quickCheck test_UnifyFunctionCanUnifyEvenLonger
