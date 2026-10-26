#!/bin/sh
# Look up the generated MoonBit signature for Lisp names: tools/sig.sh name...
for n in "$@"; do
  awk -F'\t' -v n="$n" '$1==n {print $1 "  [" $2 " " $3 "]\n    " $4}' "$(dirname "$0")/../docs/index/functions.tsv"
done
