-----------------------------------------------------------------------------------------

import           Control.Monad   (liftM, liftM2, liftM3)
import           Data.Set        as Set
import           Test.QuickCheck
import           TypeChecker

-----------------------------------------------------------------------------------------

-- Expected error messages. DON'T CHANGE THESE!
errorIfBranches :: String
errorIfBranches = "Type error: the two branches of an `if` must have the same type."
errorIfCondition :: String
errorIfCondition = "Type error: the condition of an `if` must be boolean."
errorCallNotAFunction :: String
errorCallNotAFunction = "Type error: first expression in a function call must be a function."
errorCallWrongArgNumber :: String
errorCallWrongArgNumber = "Type error: function called with the wrong number of arguments."
errorCallWrongArgType :: String
errorCallWrongArgType = "Type error: function called with an argument of the wrong type."
errorUnboundIdentifier :: String
errorUnboundIdentifier = "Error: unbound identifier."
errorTypeUnification :: String
errorTypeUnification = "Type error: inconsistent set of type constraints generated during type inference."

-----------------------------------------------------------------------------------------

--- Mocks of expressions
--- Here are a set of valid expressions to choose from when we need to generate one.
instance Arbitrary Expr where
    arbitrary =
        oneof [
            fmap IntLiteral arbitrary
            , fmap BoolLiteral arbitrary
            -- , fmap Identifier arbitrary
            , do
                x <- choose (-100000, 100000)
                y <- choose (-100000, 100000)
                return $ Call (Identifier "-") [IntLiteral x, IntLiteral y]
            , do
                x <- choose (-100000, 100000)
                y <- choose (-100000, 100000)
                return $ Call (Identifier "quotient") [IntLiteral x, IntLiteral y]
            , do
                x <- choose (-100000, 100000)
                y <- choose (-100000, 100000)
                return $ Call (Identifier "<") [IntLiteral x, IntLiteral y]
            , do
                x <- choose (True, False)
                y <- choose (True, False)
                return $ Call (Identifier "and") [BoolLiteral x, BoolLiteral y]
            , do
                x <- choose (True, False)
                return $ Call (Identifier "not") [BoolLiteral x]
            , do
                x <- choose (True, False)
                return $ Call (Identifier "not") [Call (Identifier "not") [BoolLiteral x]]
            , do
                x <- arbitrary
                return $ Call (Identifier "identity") [x]
            , do
                x <- choose (-100000, 100000)
                return $ Lambda ["x"] (Call (Identifier "+") [Identifier "x", IntLiteral x])
            , do
                x <-choose (-100000, 100000)
                y <-choose (-100000, 100000)
                return $ Lambda [] (Call (Identifier "+") [IntLiteral x, IntLiteral y])
            , do
                x <- choose (-100000, 100000)
                return $ Lambda ["x", "y"] (Call (Identifier "+") [Identifier "x", IntLiteral x])
            ,   Lambda ["x", "y", "z"] <$> arbitrary

        ]

isBool:: Expr -> Bool
isBool x = runTypeCheck ( JustExpr x ) == Right Bool_

-----------------------------------------------------------------------------------------

-- | Sample tests for `If`.

test_IfCorrect :: Bool -> Expr -> Bool
test_IfCorrect x y =
    runTypeCheck (JustExpr $ If (BoolLiteral x) y y) ==
    runTypeCheck (JustExpr y)

test_IfBadCondition :: Int -> Expr -> Bool
test_IfBadCondition x y =
    runTypeCheck (JustExpr $ If (IntLiteral 10) y y) ==
    Left errorIfCondition

test_IfBadBranches :: Expr -> Bool
test_IfBadBranches x =
    if isBool x
    then
        runTypeCheck (JustExpr $ If (BoolLiteral True) (IntLiteral 5) x)
        == Left errorIfBranches
        &&
        runTypeCheck (JustExpr $ If (BoolLiteral True) x (IntLiteral 5))
        == Left errorIfBranches
    else
        runTypeCheck (JustExpr $ If (BoolLiteral True) x (BoolLiteral True))
        == Left errorIfBranches


-- Propagate error upwards.
test_IfSubExprError :: Expr -> Bool
test_IfSubExprError x =
    if isBool x
    then
        runTypeCheck (JustExpr $
                        If (BoolLiteral True)
                           (IntLiteral 3)
                           (If (IntLiteral 10) (IntLiteral 3) (IntLiteral 4)))
        == Left errorIfCondition
    else
        runTypeCheck (JustExpr $
                        If (BoolLiteral True)
                           (IntLiteral 3)
                           (If x (IntLiteral 3) (IntLiteral 4)))
        == Left errorIfCondition


-- | Sample tests for `Call`.
test_CallCorrect :: Int -> Int -> Bool
test_CallCorrect x y =
    runTypeCheck (JustExpr $
        Call (Identifier "<") [IntLiteral x, IntLiteral y]) ==
    Right Bool_

test_CallNotAFunction :: Expr -> Expr -> Bool
test_CallNotAFunction x y =
    runTypeCheck (JustExpr $
        Call (BoolLiteral True) [x, y]) ==
    Left errorCallNotAFunction

test_CallWrongArgNumber :: Int -> Bool
test_CallWrongArgNumber x =
    runTypeCheck (JustExpr $
        Call (Identifier "remainder") [IntLiteral x]) ==
    Left errorCallWrongArgNumber

test_CallWrongArgType :: Expr -> Bool
test_CallWrongArgType x =
    if isBool x
    then runTypeCheck (JustExpr $
            Call (Identifier "or") [IntLiteral 10, BoolLiteral True]) ==
            Left errorCallWrongArgType
    else runTypeCheck (JustExpr $
            Call (Identifier "or") [BoolLiteral True, x]) ==
            Left errorCallWrongArgType

test_SomeNastyLookingShit =
    runTypeCheck (JustExpr $ Lambda ["x", "y"] (Call (Identifier "and") [Call (Identifier "<") [Identifier "x", Identifier "y"], Call (Identifier "<") [Identifier "x", Identifier "y"]]))
    ==
    Right (Function [TypeVar "tvar_x",TypeVar "tvar_y"] Bool_)


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

test_SimplyUnbound =
    runTypeCheck(JustExpr (Identifier "x"))
    == Left errorUnboundIdentifier

test_IfUnbound =
    runTypeCheck(JustExpr (If (BoolLiteral True) (Identifier "x") (Identifier "x")))
    == Left errorUnboundIdentifier

test_CallUnbounded =
    runTypeCheck(JustExpr (Call (Identifier "not") [Identifier "x"]))
    == Left errorCallWrongArgType
    || runTypeCheck(JustExpr (Call (Identifier "not") [Identifier "x"]))
    == Left errorUnboundIdentifier

-- test_BoundBeforeUnbounded =
--     runTypeCheck (JustExpr $
--                     If (BoolLiteral True)
--                        (Lambda ["x"] (BoolLiteral True))
--                        (Identifier "x")
--     == Left errorUnboundIdentifier

-----------------------------------------------------------------------------------------

main :: IO ()
main = do
    putStrLn "\n === If cases ==="
    quickCheck test_IfCorrect
    quickCheck test_IfBadCondition
    quickCheck test_IfBadBranches
    quickCheck test_IfSubExprError

    putStrLn "\n === Unbounded Identifiers ==="
    quickCheck test_SimplyUnbound
    quickCheck test_IfUnbound
    quickCheck test_CallUnbounded -- Which error do we throw?
    -- quickCheck test_BoundBeforeUnbounded --- || test_BoundBeforeUnbounded2

    putStrLn "\n === Functions"
    quickCheck test_CallCorrect
    quickCheck test_CallNotAFunction
    quickCheck test_CallWrongArgNumber
    quickCheck test_CallWrongArgType

    putStrLn "\n === Some define stuff"
    quickCheck test_DefineOne
    quickCheck test_DefineTwo

    putStrLn "\n === What is this?"
    quickCheck test_SomeNastyLookingShit

    putStrLn "\n"

-----------------------------------------------------------------------------------------
