#!/bin/sh
# Group-level relative-inertia test: rank-3 B (control) versus rank-2 B.
cd "$(dirname "$0")"
{
echo '# rank 3 control'
python3 ri_test.py 5000 1 3 4 2 3 1 4 | tail -1
python3 ri_test.py 5000 3 3 5 2 3 1 5 1 | tail -1
echo '# rank 2'
python3 ri_test.py 20000 2 2 4 2 3 1 4
python3 ri_test.py 20000 4 2 6 2 4 1 6
python3 ri_test.py 20000 5 2 6 1 4 1 6
python3 ri_test.py 20000 6 2 6 3 4 2 6
python3 ri_test.py 20000 7 2 8 2 5 2 8
python3 ri_test.py 20000 8 2 8 3 3 3 8
python3 ri_test.py 20000 9 2 6 2 4 1 6 1
python3 ri_test.py 20000 10 2 8 2 5 2 8 1
python3 ri_test.py 10000 11 2 10 3 4 2 10 1
} > ri_test.txt 2>&1
