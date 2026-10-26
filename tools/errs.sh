#!/bin/sh
moon check --output-json "$@" 2>&1 | python3 "$(dirname "$0")/errs.py" ${LIM:-60}
