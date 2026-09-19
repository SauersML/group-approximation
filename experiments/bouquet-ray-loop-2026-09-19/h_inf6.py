#!/usr/bin/env python3
"""Second pass of the infinite-order search of h_finite.py: for the recursions left undecided in
h_inf.out, test every cyclically reduced word of length 5 or 6 in S, T with the power-section-graph
certificate of same_point_screen.py.
Run: nice -n 10 timeout 1200 python3 h_inf6.py > h_inf6.out
"""
from bouquets import bouquets
from h_finite import words_ST
from same_point_screen import infinite_order

und = set(l.split(" ", 1)[1].split(" | ")[0] for l in open("h_inf.out") if " | undecided" in l)
if __name__ == "__main__":
    for k, (n, R, I) in enumerate(bouquets()):
        if n not in und: continue
        res = "undecided"
        for lab, w in words_ST(I, 6):
            if len(lab) < 5: continue
            c = infinite_order(R, w)
            if c: res = f"infinite ord({lab})=inf {c}"; break
        print(k, n, "|", res, flush=True)
