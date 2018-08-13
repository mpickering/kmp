{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE BangPatterns  #-}
module KMP where

import Debug.Trace
import Language.Haskell.TH.Lib
import Language.Haskell.TH.Syntax
import Language.Haskell.TH
import qualified Data.Map as M
import Control.Monad.State hiding (lift)

import Debug.Trace


{-
The difficulty with KMP is that it's a corecursive algorithm.

This means that it's not possible stage naively and that the recursive call
must be memoised in order to ensure termination of the code generation.

This difficulty is highlighted by the TvL version where we end up in some contortion
where everything becomes dynamic.


-}

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
This is corecursive so staging fails horribly
-}

data KMPS a = KMPS { done_s :: Code Bool, next_s :: Code a -> Code [a] -> Code Bool }

kmp_tv_s :: String -> Code String -> Code Bool
kmp_tv_s as bs = match_s (makeTable_s as) bs

match_s :: KMPS Char -> Code String -> Code Bool
match_s table s = Code [|| case $$(runCode s) of
                            [] -> $$(runCode $ done_s table)
                            (b:bs) -> $$(runCode $ done_s table)
                                      || $$(runCode (next_s table (Code [|| b ||]) (Code [|| bs ||]))) ||]

makeTable_s :: String -> KMPS Char
makeTable_s xs = init_memo table
  where table = mfix (\a -> (makeTable'_s xs (\s -> next_s a)))

true = Code [|| True ||]
false = Code [|| False ||]

liftT :: Lift a => a -> Code a
liftT = Code . unsafeTExpCoerce . lift

type M a = State (M.Map String (Code Char -> Code String -> Code Bool)) a

type S = M.Map String (Code Char -> Code String -> Code Bool)




makeTable'_s :: String -> (S -> Code Char -> Code [Char] -> Code Bool) -> M (KMPS Char)
makeTable'_s [] failure = get >>= \s -> return $ KMPS true (failure s)
makeTable'_s pat@(x:xs) failure = do
    s <- get
    !_ <- traceShowM (M.keys s)
    !_ <- traceShowM ("pat", pat)
    case M.lookup pat s of
      Just f -> return $ KMPS false f
      Nothing -> return $ KMPS false
        (down2 $ Code [|| let f c cs = $$(runCode $ test (M.insert pat (down2 $ Code [|| f ||])s) (Code [|| c ||]) (Code [|| cs ||]))
                  in f ||])
  where test :: S -> Code Char -> Code String -> Code Bool
        test s c cs =
          let success = match_s (resume s $ makeTable'_s xs (\s _ xs -> failure s (liftT x) xs)) cs
          in
          Code $ do
             runIO (putStrLn (x:xs))
             [|| if $$(runCode c) == x then $$(runCode success) else $$(runCode $ failure s c cs) ||]



up ::  (Code a -> Code b) -> Code (a -> b)
up f = Code [|| \a -> $$(runCode $ f (Code [|| a ||])) ||]

up2 f = Code [|| \a b -> $$(runCode $ f (Code [|| a ||]) (Code [|| b ||])) ||]

down  :: Code (a -> b) -> Code a -> Code b
down (Code f) (Code a) = Code [|| $$(f) $$(a) ||]

down2 :: Code (a -> b -> c) -> Code a -> Code b -> Code c
down2 f a b = down (down f a) b
