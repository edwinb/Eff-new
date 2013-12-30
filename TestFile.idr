module Main

import Effects
import Effect.File
import Effect.StdIO

data Test : Type where

readFile : Eff IO () [Test ::: FILE_IO (OpenFile Read), STDIO]
readFile = if !(Test :- eof) then return ()
              else do putStrLn !(Test :- readLine)
                      readFile

read : String -> Eff IO () [Test ::: FILE_IO (), STDIO]
read f = do x <- Test :- open f Read
            case x of
                 False => return ()
                 True => do readFile
                            Test :- close 

main : IO ()
main = run [Test := (), ()] (read "test")


