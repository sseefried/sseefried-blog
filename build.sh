#!/bin/bash

BASE="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"


mkdir -p $BASE/site
mkdir -p $BASE/site/drafts

cd $BASE/src
for src in *.md drafts/*.md; do
  POST_DIR=$(dirname $src)
  OUT=$(basename $src .md).html
  CSS=$(realpath --relative-to $POST_DIR $BASE/src)/css
  pandoc --lua-filter $BASE/fix-links.lua -s \
    --metadata="postDir:$POST_DIR" \
    --metadata="baseDir:$BASE" \
    --filter $BASE/pandoc-filters/AgdaSnippet.hs \
    -c "$CSS/style.css" \
    -c "$CSS/Agda.css" \
    $src -o $BASE/site/$POST_DIR/$OUT
done
