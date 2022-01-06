#!/bin/bash

cd src

for src in *.md; do
  OUT=$(basename $src .md).html
  pandoc --lua-filter ../fix-links.lua -s -c css/default.css $src -o ../site/$OUT
done
