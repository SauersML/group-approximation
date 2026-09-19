"""Cross-check: the C pricer (halfcube_price.c, mode all) against the exact
Fraction pricer halfcube_price.py, as sets of price vectors, for k = 2, 3, 4.

usage: python3 crosscheck.py path/to/compiled/hcp
"""
import subprocess, sys
from fractions import Fraction
from halfcube_price import all_price_vectors

for k in (2, 3, 4):
    K = 1 << k
    out = subprocess.run([sys.argv[1], str(k), "all"], capture_output=True, text=True).stdout
    c_set = {tuple(Fraction(int(v), 1 << K) for v in line.split()) for line in out.splitlines() if line.strip()}
    py_set = {tuple(Fraction(v) for v in row) for row in all_price_vectors(k)}
    print("k", k, "C classes", len(c_set), "python classes", len(py_set), "equal", c_set == py_set)
