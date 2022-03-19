#!/bin/bash

THIS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}" )" && pwd)"
ABS_AGDA_SRC="$THIS_DIR/agda-src"
ABS_AGDA_HTML="$THIS_DIR/site/agda-html"

#
# Each sub-directory in agda-src should contain a module called Entrypoint.agda
# that just imports all the files necessary to generate the source files you need.
#

cd $ABS_AGDA_SRC
for relsrcdir in *; do
  if [ -d "$relsrcdir" ]; then
    cd $relsrcdir
    if [ ! -f Entrypoint.agda ]; then
      echo "[ERROR] Could not find Entrypoint.agda in $relsrcdir"
    else
      agda --html Entrypoint.agda --html-dir="$ABS_AGDA_HTML/$relsrcdir"
    fi
    cd $ABS_AGDA_SRC
  fi
done
