#!/bin/bash

BASE="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"


mkdir -p $BASE/site
mkdir -p $BASE/site/drafts

cd $BASE/src
for src in *.md drafts/*.md; do
  if [ "$src" != "index.md" ]; then
    TEMPLATE="--template=$BASE/pandoc-data/templates/post.html"
  else
    TEMPLATE=""
  fi

  POST_DIR=$(dirname $src)
  OUT=$(basename $src .md).html
  CSS=$(realpath --relative-to $POST_DIR $BASE/src)/css
  echo "Building: $src"
  pandoc --lua-filter $BASE/fix-links.lua -s \
    $TEMPLATE \
    --metadata="postDir:$POST_DIR" \
    --metadata="baseDir:$BASE" \
    --filter $BASE/pandoc-filters/AgdaSnippet.hs \
    -c "$CSS/style.css" \
    -c "$CSS/Agda.css" \
    $src -o $BASE/site/$POST_DIR/$OUT
done
