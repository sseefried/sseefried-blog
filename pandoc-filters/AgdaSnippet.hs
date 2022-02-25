#!/usr/bin/env runhaskell

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}

-- includes.hs
import Data.List
import Text.Pandoc.JSON
import qualified Data.Text.IO as TIO
import qualified Data.Text as T
import System.Process
import System.Posix.Directory

doInclude :: Block -> IO Block
doInclude cb@(CodeBlock (id, classes, namevals) contents)
  | Just htmlSource <- lookup "htmlDir" namevals
  , Just modul <- lookup "module" namevals
  , Just (cmd, ident) <- getCmdAndIdent namevals = do
       html <- (T.pack <$>
          readProcess "../../pandoc-filters/mk-snippet-html.sh"
           (map T.unpack [ cmd , htmlSource, modul, ident ]) "")
       return $ Plain [ RawInline (Format "html")
                      ("<pre class=\"Agda\">" <> html <> "</pre>") ]
  | otherwise = return cb
  where
    getCmdAndIdent namevals
      | Just ident <- lookup "delimeters" namevals = Just ("delimeters", ident)
      | Just ident <- lookup "fun" namevals = Just ("fun", ident)
      | Just ident <- lookup "sig" namevals = Just ("sig", ident)
      | otherwise = Nothing
doInclude x = return x

main :: IO ()
main = toJSONFilter doInclude