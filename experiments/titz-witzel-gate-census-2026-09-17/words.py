#!/usr/bin/env python3
"""Generate relators.h for gate_anneal.c from the recorded two-generator word check.

The words are taken literally from research/artifacts/titz-witzel-two-generator-free-word-check.py
(definitions (TW2G1), retained relators (TW2G2)); e^2 is imposed exactly in the C code.
"""
import importlib.util
import pathlib

ROOT = pathlib.Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location(
    "w", ROOT / "research/artifacts/titz-witzel-two-generator-free-word-check.py")
w = importlib.util.module_from_spec(spec)
spec.loader.exec_module(w)

e, u = (1,), (2,)
inv = (1,)


def p(*a):
    return w.product(*a, involutions=inv)


def q(x, k):
    return w.power(x, k, involutions=inv)


I = w.inverse
h = p(u, e, I(u)); a = p(e, h, e); x = p(a, q(u, 2)); c = p(q(u, 2), a, q(u, 2))
f = p(I(x), h, x); d = p(e, I(a), f); s = p(f, a, f)
rho = p(I(x), I(s), I(c)); b = p(rho, I(u), rho)
rels = [q(c, 2), p(q(rho, 2), I(e), I(u)), p(b, x, I(u), I(d)), p(a, c, d, b)]

# Letter codes for C: e -> 1 (self-inverse), u -> 2, u^-1 -> -2.
out = ["#define NREL 4"]
for i, r in enumerate(rels):
    out.append("static const int R%d[%d] = {%s};" % (i, len(r), ",".join(str(l) for l in r)))
out.append("static const int *REL[4] = {R0,R1,R2,R3};")
out.append("static const int RLEN[4] = {%s};" % ",".join(str(len(r)) for r in rels))
(pathlib.Path(__file__).parent / "relators.h").write_text("\n".join(out) + "\n")
print("lengths", [len(r) for r in rels])
