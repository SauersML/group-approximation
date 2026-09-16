#!/usr/bin/env python3
"""Negative control: replace N_{g,h} by the constant g_1*h_2 times t^0 (the naive
trivial-coefficient cocycle, which needs an invariant functional). Check (2) must then fail
for the translation toy model, showing the test is not vacuous."""
import verify_cocycle as V


def naive(g, h):
    v = g[0] * h[1]
    return {(0, 0): v} if v else {}


V.Ncoef = naive
try:
    V.check_tau_b(trials=200)
    print("naive cocycle PASSED (unexpected)")
except AssertionError:
    print("naive cocycle fails tau o b = 0, as expected")
