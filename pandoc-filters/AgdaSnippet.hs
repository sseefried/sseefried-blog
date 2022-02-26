#!/usr/bin/env runhaskell

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}

import Data.List
import Text.Pandoc.JSON
import qualified Data.Text.IO as TIO
import qualified Data.Text as T
import System.IO (stderr)
import System.Process (readProcess)
import System.Posix.Directory

errP :: T.Text -> IO ()
errP txt = TIO.hPutStr stderr (txt <> "\n")

errP' :: String -> IO ()
errP' = errP . T.pack

doBlock :: (T.Text, T.Text) -> (Block -> IO Block)
doBlock (postDir, baseDir) cb@(CodeBlock (id, classes, namevals) contents)
  | Just htmlDir <- lookup "htmlDir" namevals
  , Just modul <- lookup "module" namevals
  , Just (cmd, ident) <- getCmdAndIdent namevals = do
       html <-
         case cmd of
           "inprogress" -> do
              file <- TIO.readFile $ T.unpack $ baseDir <> "/agda-html/" <>
                        htmlDir <> "/" <> modul <> ".html"
              return "<div></div>"
           _ -> do
              (T.pack <$>
               readProcess (T.unpack baseDir ++ "/pandoc-filters/mk-snippet-html.sh")
               (map T.unpack [ postDir, cmd , htmlDir, modul, ident ]) "")
       return $ Plain [ RawInline (Format "html")
                      ("<pre class=\"Agda\">" <> html <> "</pre>") ]
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

main :: IO ()
main = toJSONFilter doPandoc
