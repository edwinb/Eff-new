module Main

import Effects
import Effect.File
import Effect.StdIO

data Test : Type where

readFile : { [Test ::: FILE_IO (OpenFile Read), STDIO] } EffM IO ()
readFile = if !(Test :- eof) then return ()
              else do putStrLn !(Test :- readLine)
                      readFile

read : String -> { [Test ::: FILE_IO (), STDIO] } EffM IO ()
read f = do case !(Test :- open f Read) of
                 False => return ()
                 True => do readFile
                            Test :- close 

main : IO ()
main = run [Test := (), ()] (read "test")


