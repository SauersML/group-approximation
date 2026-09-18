#!/usr/bin/env python3
"""Solve the one-bit linear-atom LP from the binary columns written by atom_gen.c.

usage: atom_bin_lp.py target.txt atoms.bin out.json
Minimises sum_a w_a phi_a subject to sum_a w_a = 1, w >= 0 and the (T) rows sum_a w_a (h_a(S) - h_a(rep S)) = 0.
Duplicate columns are merged. Writes the value and the optimal support (atom index, weight) to out.json; the atom
index decodes as in atom_gen.c (mixed radix over the codewords' read sets).
"""
import sys, json
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import csc_matrix

hdr = np.fromfile(sys.argv[2], dtype=np.int32, count=2)
na, nc = int(hdr[0]), int(hdr[1])
M = np.fromfile(sys.argv[2], dtype=np.int8, offset=8).reshape(na, nc)
U, idx = np.unique(M, axis=0, return_index=True)
print('atoms', na, 'distinct columns', len(U), 'rows', nc - 1, flush=True)
c = U[:, 0].astype(float)
A = U[:, 1:].T.astype(float)
A = np.vstack([A, np.ones((1, len(U)))])
b = np.zeros(A.shape[0]); b[-1] = 1.0
res = linprog(c, A_eq=csc_matrix(A), b_eq=b, bounds=(0, None), method='highs')
print('status', res.status, 'value', res.fun)
sup = [(int(idx[i]), float(res.x[i])) for i in np.nonzero(res.x > 1e-10)[0]] if res.status == 0 else []
json.dump(dict(value=res.fun, status=int(res.status), support=sup), open(sys.argv[3], 'w'))
