#!/bin/bash

THIS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}" )" && pwd)"
ABS_AGDA_SRC="$THIS_DIR/agda-src"
ABS_AGDA_HTML="$THIS_DIR/site/agda-html"

cd $ABS_AGDA_SRC
for relsrcdir in *; do
  if [ -d "$relsrcdir" ]; then
    cd $relsrcdir
    agda --html Permutations.agda --html-dir="$ABS_AGDA_HTML/$relsrcdir"
    cd $ABS_AGDA_SRC
  fi
done
