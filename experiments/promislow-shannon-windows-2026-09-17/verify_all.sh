#!/bin/sh
# Exact verification of every new minimal-window Shannon fake; run from this directory.
# Each line must print ALL EXACT and exit 0.
set -e
python3 verify_generic.py k2 "[(0,0),(1,0),(0,1),(1,1)]" "[(0,0),(1,1),(0,1)]"
python3 verify_generic.py k2 "[(0,0),(1,0),(1,1)]" "[(1,1),(1,0),(0,1)]"
python3 verify_generic.py dinf "[(1,0),(-1,0),(-1,1),(1,1)]" "[(-1,1),(1,-1),(1,0),(1,1)]"
python3 verify_generic.py cyc7 "[0,1,2,4]" "[0,3,5,6]" 5000
python3 verify_generic.py cyc7 "[0,1,2,5]" "[0,5,2,1]" 5000
echo "# all fakes verified"
