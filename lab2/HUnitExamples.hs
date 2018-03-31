import Test.HUnit

run = runTestTT tests
tests = TestList [TestLabel "test1" test1, TestLabel "test2" test2]

test1 = TestCase (assertEqual "aaa" 3 (1 + 3))
-- test2 = TestCase (do (x,y) <- partA 3
--                      assertEqual "for the first result of partA," 5 x
--                      b <- partB y
--                      assertBool ("(partB " ++ show y ++ ") failed") b)

test2 = TestCase (assertEqual "bbb" 1 1)