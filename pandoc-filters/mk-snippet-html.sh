#!/bin/bash

#
# Dodgy script that will get replaced
#

THIS_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
SITE_DIR="$( cd $THIS_DIR/../site && pwd)"
cd $THIS_DIR

[ $# -lt 4 ] && { echo "Usage: $(basename $0) <cmd> <basedir> <module> <id>"; exit 1;}

CMD=$1
BASE=$(cd $SITE_DIR/agda-html/$2 && pwd)
MODULE=$3
# Need to escape certain special characters
ID=$(echo $4 | sed 's/\[/\\[/g' | sed 's/\]/\\]/g' | sed 's/\+/\\+/g')

#
# FIXME: Handle drafts properly
#
BASE_RELATIVE=$(realpath --relative-to=$SITE_DIR/drafts $BASE | sed 's/\//\\\//g' | sed 's/\./\\./g')

cd "$BASE"

case "$CMD" in
  delimeters)
    # FIXME: Use of dodgy greater than sign at end
    OUT=$(cat "$MODULE.html" | sed -n "/--pandoc-begin $ID</,/--pandoc-end $ID</p" \
      | grep -v '\-\-pandoc')
    ;;

  fun)
     OUT=$(cat "$MODULE.html" \
       | sed -E -n "/^<a id=\"$ID\"/,/<a id=\"[^0-9]/{ /a id=\"$ID\"/p ; /<a id=\"[^0-9]/d; /^<a id=\"[^\"]*\" class=\"Comment\"/d; p;  }")
     ;;

  sig)
     OUT=$(cat "$MODULE.html" \
       | sed -n "/<a id=\"$ID\"/p")
    ;;

  *)
    exit 1
    ;;
esac

echo "$OUT" | sed "s/href=\"\([^\"]*\)\"/href=\"$BASE_RELATIVE\/\\1\"/g"
