{-# LANGUAGE TemplateHaskell #-}
module KMP where

import Debug.Trace
import Language.Haskell.TH.Lib
import Language.Haskell.TH
import qualified Data.Map as M
import Control.Monad.State

type MemoTable a b = M.Map a (Code b)

type Memo a b r = State (MemoTable a b) r

--memoise :: String -> (Code r -> Memo String r (Code r))
--                  -> Memo String r (Code r)
--                  -> Memo String r (Code r)
memoise key call fcn = do
  table <- get
  case M.lookup key table of
    Just f -> call f
    Nothing ->
      return
        (Code [|| let f = $$(runCode $ run_memo fcn (M.insert key (Code [|| f ||]) table))
                  in $$(runCode $ run_memo (call (Code [|| f ||])) table) ||])

run_memo = evalState

init_memo m = evalState m M.empty

save f = get >>= \s -> return (f s)
resume s m = run_memo m s


newtype Code a = Code (Q (TExp a))

runCode (Code a) = a

search :: String -> String -> Bool
search pat s = go pat s pat s
  where
    go pat s op os =
          case pat of
            [] -> True
            (p:ps) ->
              case s of
                [] -> False
                (s1:ss) ->
                  if  p == s1 then go ps ss op os
                              else case os of
                                         [] -> False
                                         (_:ss) -> search op os

fix f = let x = f x in x

search_s :: String -> Code (String -> Bool)
search_s pat = Code [|| \s -> $$(runCode $ init_memo (go pat (Code [|| s ||]) pat (Code [|| s ||]))) ||]
  where
    go :: String -> Code String -> String -> Code String ->
            Memo String (String -> String -> Bool) (Code Bool)
    go pat (Code s) op (Code os) =
          case pat of
            [] -> return (Code [|| True ||])
            (p:ps) ->
                let call = (\(Code f) -> return (Code [|| $$(f) $$(s) $$(os) ||]))
                in memoise pat call
                  (save
                    (\state -> Code [|| \ss os ->
                                          case ss of
                                            [] -> False
                                            (s:ss) ->
                                              if p == s
                                                then $$(runCode $ resume state (go ps (Code [|| ss ||]) op (Code ([|| os ||]))))
                                                else $$(runCode $ resume state (next op (Code ([|| os ||])))) ||]))

    next :: String -> Code String -> Memo String (String -> String -> Bool) (Code Bool)
    next op (Code os) =
      save (\state -> Code [|| case $$(os) of
                                  [] -> False
                                  (s:ss) -> $$(runCode $ resume state (go op (Code [|| ss ||]) op (Code [|| ss ||])))
                            ||])



            {-
              (Code [||
              case $$(s) of
                [] -> False
                (s1:ss) ->
                  if  p == s1 then go ps ss op os
                              else case os of
                                         [] -> False
                                         (_:ss) -> search op os ||])
                                         -}

data KMP a = KMP { done :: Bool, next :: a -> KMP a }


kmp_tv :: String -> String -> Bool
kmp_tv as bs = match (makeTable as) bs
  where
    match table [] = done table
    match table (b:bs) = done table || match (next table b) bs

makeTable :: String -> KMP Char
makeTable xs = table
  where table = makeTable' xs (const table)

makeTable' [] failure = KMP True failure
makeTable' (x:xs) failure = KMP False test
  where test c = if c == x then success else failure c
        success = makeTable' xs (next (failure x))


{-
data KMPS a = KMPS { done_s :: Code Bool, next_s :: Code a -> Code (KMPS a) }

kmp_tv_s :: String -> Code String -> Code Bool
kmp_tv_s as bs = match (makeTable_s as) bs
  where
    match :: KMPS Char -> Code String -> Code Bool
    match table s = Code [|| case $$(runCode s) of
                                [] -> $$(runCode $ done_s table)
                                (b:bs) -> $$(runCode $ done_s table)
                                          || $$(runCode $ match (next_s table (Code [|| b ||])) (Code [|| bs ||])) ||]

makeTable_s :: String -> KMPS Char
makeTable_s xs = table
  where table = makeTable'_s xs (const table)

true = Code [|| True ||]
false = Code [|| False ||]

makeTable'_s :: String -> (Code a -> KMPS a) -> KMPS Char
makeTable'_s [] failure = KMPS true failure
makeTable'_s (x:xs) failure = KMPS false test
  where test :: Code Char -> Code (KMPS Char)
        test c = if c == x then success else failure c
        success = makeTable'_s xs (next (failure x))
-}



up ::  (Code a -> Code b) -> Code (a -> b)
up f = Code [|| \a -> $$(runCode $ f (Code [|| a ||])) ||]

down  :: Code (a -> b) -> Code a -> Code b
down (Code f) (Code a) = Code [|| $$(f) $$(a) ||]

down2 :: Code (a -> b -> c) -> Code a -> Code b -> Code c
down2 f a b = down (down f a) b
