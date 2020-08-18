import Core.Core

coreProg : Core ()
coreProg
    = do coreLift $ putStr "Name: "
         n <- coreLift $ getLine
         coreLift $ putStrLn $ "Hello " ++ n
         coreProg

coreMain : Core ()
coreMain
    = coreProg

main : IO ()
main = coreRun coreMain
               (\err => putStrLn "It went wrong")
               pure
