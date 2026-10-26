#!/bin/sh
# Fetch the Maxima source tree this port was translated from (and reads its
# share packages, tests and Lisp sources from at run time) into .repos/maxima,
# or into the directory given as the first argument.
set -e
COMMIT=81531b1da08855d2ef93965003834b69ec4905af
DIR="${1:-$(cd "$(dirname "$0")/.." && pwd)/.repos/maxima}"
if [ ! -d "$DIR/.git" ]; then
  mkdir -p "$DIR"
  git -C "$DIR" init -q
  git -C "$DIR" remote add origin https://github.com/calyau/maxima.git
fi
git -C "$DIR" fetch -q --depth 1 origin "$COMMIT"
git -C "$DIR" checkout -q --detach FETCH_HEAD
echo "Maxima source tree at $COMMIT in $DIR"
