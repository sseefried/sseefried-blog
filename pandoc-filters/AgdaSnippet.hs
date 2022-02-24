#!/usr/bin/env runhaskell

{-# LANGUAGE OverloadedStrings #-}

-- includes.hs
import Data.List
import Text.Pandoc.JSON
import qualified Data.Text.IO as TIO
import qualified Data.Text as T
import System.Process
import System.Posix.Directory

doInclude :: Block -> IO Block
doInclude cb@(CodeBlock (id, classes, namevals) contents) = do
  case ( lookup "htmlDir" namevals
       , lookup "module" namevals
       , lookup "def" namevals) of
    (Just htmlSource, Just modul, Just def) -> do
          html <- (T.pack <$>
                    readProcess "../../pandoc-filters/mk-snippet-html.sh"
                    (map T.unpack [ htmlSource, modul, def ]) "")
          return $ Plain [ RawInline (Format "html")
                      ("<pre class=\"Agda\">" <> html <> "</pre>") ]
    _          -> do
         return cb
doInclude x = return x

main :: IO ()
main = toJSONFilter doInclude