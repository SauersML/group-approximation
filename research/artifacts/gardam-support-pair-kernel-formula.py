#!/usr/bin/env python3
"""Check kappa_i = |S cap g_i T g_i| - 1 at the 17 trivial units on (S, T)."""
import io, contextlib
buf = io.StringIO()
with contextlib.redirect_stdout(buf):
    exec(open("gsp.py").read())
for i in range(21):
    for j in range(21):
        if mul(S[i], T[j]) == E:
            gi = S[i]
            conj = set(mul(mul(gi, h), gi) for h in T)
            print("trivial pair", i, j, "|S cap g_i T g_i| - 1 =", sum(1 for g in S if g in conj) - 1)
