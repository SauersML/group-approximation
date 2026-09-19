#!/usr/bin/env python3
"""Counting certificates on small regular (Cayley) L-sets V = Q, K -> Q onto."""
import random, sys, math
sys.path.insert(0, '.')
from foldgroup import *

rng = random.Random(99)
G = small_groups()
for qn in ['S3', 'A4', 'SL23', 'S4', 'A5']:
    Q = G[qn]; seen = 0
    for _ in range(400):
        beta, gamma = rng.choice(Q), rng.choice(Q)
        alpha = pmul(pmul(pinv(beta), gamma), pmul(beta, beta))
        if len(closure([beta, gamma])) != len(Q) or len(closure([gamma, alpha])) != len(Q):
            continue
        seen += 1
        if seen > 3:
            break
        Pb, Pc, n = regular_lset(beta, gamma)
        print(report(f"{qn} regular", Pb, Pc, rng, G,
                     ['C2', 'C3', 'S3', 'A4', 'SL23', 'S4', 'A5']), flush=True)
