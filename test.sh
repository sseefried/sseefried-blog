#!/bin/bash

BASE="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"

cd $BASE/src/drafts

mkdir -p $BASE/site/drafts
for src in agda-snippets-test.md; do
  OUT=$(basename $src .md).html
  pandoc --lua-filter $BASE/fix-links.lua \
    --filter ../../pandoc-filters/AgdaSnippet.hs \
    -s -c ../css/default.css $src -o $BASE/site/drafts/$OUT
done

cd $BASE

cat site/drafts/agda-snippets-test.html
