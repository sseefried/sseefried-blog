#!/usr/bin/env runhaskell

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}

import Prelude
import Data.List
import qualified Data.List as L
import Text.Pandoc.JSON
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import System.IO (stderr)
import System.Process (readProcess)
import System.Posix.Directory

errP :: Text -> IO ()
errP txt = TIO.hPutStr stderr (txt <> "\n")

errP' :: String -> IO ()
errP' = errP . T.pack

doBlock :: (Text, Text) -> (Block -> IO Block)
doBlock (postDir, baseDir) cb@(CodeBlock (id, classes, namevals) contents)
  | Just htmlDir <- lookup "htmlDir" namevals
  , Just modul <- lookup "module" namevals
  , Just (cmd, ident) <- getCmdAndIdent namevals = do
       inHtml <- TIO.readFile $ agdaHtmlFilepath baseDir htmlDir modul
       let
         htmlFilter =
           case cmd of
             "delimeters" ->
                delimitedCodeBlock ident
             "fun" ->
                case lookup "lines" namevals of
                   Just n -> functionDef ident (read (T.unpack n))
                   Nothing -> const ""
             "sig" ->
               signatureOf ident
             _ -> const ""
       let outHtml = fixLinks postDir htmlDir .  htmlFilter $ inHtml
       return $ Plain [ RawInline (Format "html")
                      ("<pre class=\"Agda\">" <> outHtml <> "</pre>") ]
  | otherwise = return cb
  where
    getCmdAndIdent namevals
      | Just ident <- lookup "delimeters" namevals = Just ("delimeters", ident)
      | Just ident <- lookup "fun" namevals = Just ("fun", ident)
      | Just ident <- lookup "sig" namevals = Just ("sig", ident)
      | otherwise = Nothing
doBlock _ x = return x

doPandoc :: Pandoc -> IO Pandoc
doPandoc pandoc@(Pandoc meta blocks) = do
--  errP' $ show meta
  case (lookupMeta "postDir" meta, lookupMeta "baseDir" meta) of
    (Just (MetaString postDir), Just (MetaString baseDir)) -> do
      blocks' <- mapM (doBlock (postDir, baseDir)) blocks
      return $ Pandoc meta blocks'
    _ -> error "Could not find meta data with keys 'postDir' and/or 'baseDir'"


agdaHtmlFilepath :: Text -> Text -> Text -> String
agdaHtmlFilepath baseDir htmlDir modul =
  T.unpack $ baseDir <> "/site/agda-html/" <> htmlDir <> "/" <> modul <> ".html"

type Filter = Text -> Text


lineFilter :: ([Text] -> [Text]) -> Filter
lineFilter f = T.unlines . f . T.lines

delimitedCodeBlock :: Text -> Filter
delimitedCodeBlock ident = lineFilter $
  L.filter (not . T.isInfixOf "--pandoc-begin") . -- remove nested delimeters
  L.filter (not . T.isInfixOf "--pandoc-end") .   -- remove nested delimeters
  linesBetweenDelimeters ("--pandoc-begin " <> ident <> "</a>",
                          "--pandoc-end " <> ident <> "</a>")

linesBetweenDelimeters :: (Text, Text) -> [Text] -> [Text]
linesBetweenDelimeters (start, finish) =
   L.takeWhile (not . T.isInfixOf finish) .
   L.drop 1 .
   L.dropWhile (not . T.isInfixOf start)

functionDef :: Text -> Int -> Filter
functionDef ident n = lineFilter $
  L.take n .
  L.dropWhile  (not . T.isPrefixOf ("<a id=\"" <> ident <> "\"></a>"))

signatureOf :: Text -> Filter
signatureOf ident = functionDef ident 1

fixLinks :: Text -> Text -> Filter
fixLinks postDir htmlDir =
    T.replace "href=\""
      (  "href=\""
      <> if postDir == "." then "." else ".."
      <> "/agda-html/"
      <> htmlDir
      <> "/")


main :: IO ()
main = toJSONFilter doPandoc
