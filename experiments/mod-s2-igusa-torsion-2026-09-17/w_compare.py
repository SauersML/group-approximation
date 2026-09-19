#!/usr/bin/env python3
"""Compare W(Gamma(4,8)) with W(Gamma(4)) on the common 160 classes.

    python3 w_compare.py level4.pkl res.json.pkl

level4.pkl is written by igusa_exact.py level4, res.json.pkl by
za_igusa.py census_mod.  Checks: the Igusa classes sit one over each
level-four class (identity order), W_I <= W_4 have equal rank and equal
Gram determinant (so W_I = W_4), and the order-2 torsion coordinate eps
pairs evenly with every W_4 basis vector."""
import pickle
import sys

import numpy as np
from flint import fmpz_mat

l4 = pickle.load(open(sys.argv[1], "rb"))
r = pickle.load(open(sys.argv[2], "rb"))
dist = r["distinct"]
assert [kk[0] for kk in dist] == list(range(len(l4["distinct"])))
B4 = [[int(x) for x in w] for w in l4["B4"]]
BI = [[int(x) for x in w] for w in r["B"]]
M4, MI = fmpz_mat(B4), fmpz_mat(BI)
assert M4.rank() == MI.rank() == len(B4) == len(BI)
# W_I <= W_4 holds by push-forward (fibres of size one); sanity: same Q-span
assert fmpz_mat(B4 + BI).rank() == len(B4)
g4 = (M4 * M4.transpose()).det()
gI = (MI * MI.transpose()).det()
print("rank", len(B4), "Gram det ratio", gI / g4)
Y = np.array([kk[1] for kk in dist])
eps = Y[:, 0]
assert set(eps) <= {0, 1}
odd = sum(int(np.dot(np.array(w, dtype=np.int64), eps)) % 2 for w in B4)
print("eps = 1 on", int(eps.sum()), "classes; eps . w odd for", odd, "basis vectors of W_4")
