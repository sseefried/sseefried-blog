#!/bin/bash

#
# Dodgy script that will get replaced
#

THIS_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
SITE_DIR="$( cd $THIS_DIR/../site && pwd)"
cd $THIS_DIR

[ $# -lt 3 ] && { echo "Usage: $(basename $0) <basedir> <module> <id>"; exit 1;}

BASE=$(cd $SITE_DIR/agda-html/$1 && pwd)
MODULE=$2
ID=$3

#
# FIXME: Handle drafts properly
#
BASE_RELATIVE=$(realpath --relative-to=$SITE_DIR/drafts $BASE | sed 's/\//\\\//g' | sed 's/\./\\./g')

cd "$BASE"

# FIXME: Use of dodgy greater than sign at end
cat "$MODULE.html" | sed -n "/--pandoc-begin $ID</,/--pandoc-end $ID</p" \
  | sed "s/href=\"\([^\"]*\)\"/href=\"$BASE_RELATIVE\/\\1\"/g" | grep -v '\-\-pandoc'
