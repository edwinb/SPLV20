import Core.Core

data Counter : Type where

coreProg : {auto c : Ref Counter Integer} ->
           Core ()
coreProg
    = do count <- get Counter
         coreLift $ putStr $ show count ++ " Name: "
         put Counter (count + 1)
         n <- coreLift $ getLine
         coreLift $ putStrLn $ "Hello " ++ n
         coreProg

coreMain : Core ()
coreMain
    = do c <- newRef Counter 0
         coreProg

main : IO ()
main = coreRun coreMain
               (\err => putStrLn "It went wrong")
               pure
