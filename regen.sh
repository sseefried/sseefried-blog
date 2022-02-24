#!/bin/bash

THIS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}" )" && pwd)"

cd agda-src/2022-02-24-permutations
agda --html Permutations.agda --html-dir=$THIS_DIR/site/agda-html/2022-02-24-permutations
