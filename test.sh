#!/bin/bash

BASE="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"

cd $BASE/src/drafts

mkdir -p $BASE/site/drafts
for src in proving-a-more-general-theorem-is-often-easier.md; do
  OUT=$(basename $src .md).html
  pandoc --lua-filter $BASE/fix-links.lua \
    --filter ../../pandoc-filters/AgdaSnippet.hs \
    -s \
    -c ../css/default.css \
    -c ../css/Agda.css \
    $src \
    -o $BASE/site/drafts/$OUT
done
