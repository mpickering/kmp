{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -ddump-splices #-}
module Test where

import KMP

test = $$(runCode $ search_s "abb")

test2 = $$(runCode $ up (kmp_tv_s "abb"))


