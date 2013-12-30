module Effect.File

import Effects
import Control.IOExcept

data OpenFile : Mode -> Type where
     FH : File -> OpenFile m

openOK : Mode -> Bool -> Type
openOK m True = OpenFile m
openOK m False = ()

data FileIO : Effect where
     Open  : String -> (m : Mode) -> 
             FileIO Bool () (openOK m)
     Close : FileIO () (OpenFile m) (\v => ())

     ReadLine  :           FileIO String (OpenFile Read)  (\v => (OpenFile Read))
     WriteLine : String -> FileIO ()     (OpenFile Write) (\v => (OpenFile Write))
     EOF       :           FileIO Bool   (OpenFile Read)  (\v => (OpenFile Read))


instance Handler FileIO IO where
    handle () (Open fname m) k = do h <- openFile fname m
                                    valid <- validFile h
                                    case valid of
                                         True => k True (FH h)
                                         False => k False ()
    handle (FH h) Close      k = do closeFile h
                                    k () ()
    handle (FH h) ReadLine        k = do str <- fread h
                                         k str (FH h)
    handle (FH h) (WriteLine str) k = do fwrite h str
                                         k () (FH h)
    handle (FH h) EOF             k = do e <- feof h
                                         k e (FH h)

FILE_IO : Type -> EFFECT
FILE_IO t = MkEff t FileIO

open : Handler FileIO e =>
       String -> (m : Mode) -> EffM e Bool [FILE_IO ()]
                                           (\v => [FILE_IO (openOK m v)])
open f m = Open f m

close : Handler FileIO e =>
        EffM e () [FILE_IO (OpenFile m)] (\v => [FILE_IO ()])
close = Close

readLine : Handler FileIO e => Eff e String [FILE_IO (OpenFile Read)]
readLine = ReadLine

writeLine : Handler FileIO e => String -> Eff e () [FILE_IO (OpenFile Write)]
writeLine str = WriteLine str

eof : Handler FileIO e => Eff e Bool [FILE_IO (OpenFile Read)]
eof = EOF




