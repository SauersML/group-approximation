#!/usr/bin/env python3
"""The explicit family G_k = <a,t | w_k>, k >= 1, whose Magnus word is
    W_0 = T a_0^(-k) T^(-1) a_0^(k+1),   T = a_2 a_0 a_1 a_2,   a_h = t^h a t^-h.
Prints one line per k in the OPEN format of bs_search.py, with U = T^-1, V = a_0^-1, X = a_2,
(so W_0 = U^-1 V^k U V^-(k+1)), for checking by verify.py:
    python3 family.py 8 | python3 verify.py
|w_k| = 25 + 2k."""
import sys
sys.path.insert(0, '/home/user/group-approximation/research/artifacts/or-unpeelable-census-scripts-2026-09-12')
import census as C

K = int(sys.argv[1]) if len(sys.argv) > 1 else 6
for k in range(1, K + 1):
    seq = [(2, 1), (0, 1), (1, 1), (2, 1), (0, -k), (2, -1), (1, -1), (0, -1), (2, -1), (0, k + 1)]
    w = C.cyc_reduce(C.seq_to_word(seq))
    U = [-3, -2, -1, -3]          # T^-1 = a_2^-1 a_1^-1 a_0^-1 a_2^-1
    V = [-1]                      # a_0^-1
    X = [[3]]                     # a_2
    print('OPEN', C.word_str(w), len(w), k, k + 1, repr(U).replace(' ', ''), repr(V).replace(' ', ''),
          repr(X).replace(' ', ''), repr(seq).replace(' ', ''))
