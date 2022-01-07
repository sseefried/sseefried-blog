#!/bin/bash

BASE="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"

cd $BASE/src

mkdir -p $BASE/site
for src in *.md; do
  OUT=$(basename $src .md).html
  pandoc --lua-filter $BASE/fix-links.lua -s -c /blog/css/default.css $src -o $BASE/site/$OUT
done

cd $BASE/src/drafts

mkdir -p $BASE/site/drafts
for src in *.md; do
  OUT=$(basename $src .md).html
  pandoc --lua-filter $BASE/fix-links.lua -s -c /blog/css/default.css $src -o $BASE/site/drafts/$OUT
done
