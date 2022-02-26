#!/bin/bash

#
# Dodgy script that will get replaced
#

THIS_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
BASE_DIR="$( cd $THIS_DIR/.. && pwd)"
SITE_DIR="$( cd $THIS_DIR/../site && pwd)"
cd $THIS_DIR

[ $# -lt 5 ] && { echo "Usage: $(basename $0) <postdir> <cmd> <basedir> <module> <id>"; exit 1;}

ABS_POST_DIR=$(cd $BASE_DIR/site/$1 && pwd)
CMD=$2
BASE=$(cd $SITE_DIR/agda-html/$3 && pwd)
MODULE=$4
# Need to escape certain special characters
ID=$(echo $5 | sed 's/\[/\\[/g' | sed 's/\]/\\]/g' | sed 's/\+/\\+/g')

BASE_RELATIVE=$(realpath --relative-to=$ABS_POST_DIR $BASE | sed 's/\//\\\//g' | sed 's/\./\\./g')

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
