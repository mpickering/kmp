{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -ddump-splices #-}
module Test where

import KMP

test = $$(runCode $ search_s "abb")


