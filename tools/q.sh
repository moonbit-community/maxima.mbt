#!/bin/sh
# Print the q_ constant for Lisp symbol names: tools/q.sh '$sin' mplus
cd "$(dirname "$0")" && python3 -c '
import sys, json
sys.argv=sys.argv
import gen
db=json.load(open("db.json"))
gen.compute_overrides(db)
for n in sys.argv[1:]:
    print(n, "->", gen.sym_const(n), "   (function name:", gen.fn_name(n) + ")")
' "$@"
