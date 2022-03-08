#!/bin/bash

BASE="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"

cd $BASE/src
for src in *.md drafts/*.md devlog/*.md; do
  # Exceptions for comments system
  if [ "$src" != "index.md" -a "$src" != "devlog/index.md" ]; then
    TEMPLATE="--template=$BASE/pandoc-data/templates/post.html"
  else
    TEMPLATE=""
  fi
  mkdir -p $BASE/site/$POST_DIR
  POST_DIR=$(dirname $src)
  OUT=$(basename $src .md).html
  CSS=$(realpath --relative-to $POST_DIR $BASE/src)/css
  echo "Building: $src -> $BASE/site/$POST_DIR/$OUT"
  pandoc --lua-filter $BASE/fix-links.lua -s \
    $TEMPLATE \
    --metadata="postDir:$POST_DIR" \
    --metadata="baseDir:$BASE" \
    --filter $BASE/pandoc-filters/AgdaSnippet.hs \
    -c "$CSS/style.css" \
    -c "$CSS/Agda.css" \
    $src \
    -o $BASE/site/$POST_DIR/$OUT
done
