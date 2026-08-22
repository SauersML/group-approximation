---
rg: 2
id: hamming-cosystolic-hs-mismatch-proof
kind: route
title: Compare the support metric in group-independent cosystolic expansion with normalized HS defects
target: hamming-cosystolic-misses-hs-magnitude
requires: []
---

Kaufman--Oppenheim--Weinberger, arXiv:2411.02819, Theorem 2.11 states the
uniform cosystolic conclusion for every coefficient group, but the preceding
definitions measure a cochain by the fraction of simplices on which it is
nonidentity.  Specializing the coefficient group to a unitary group does not
change that metric.

Choose bounded self-adjoint matrices `H_e` and exponentiate them by a scalar
`epsilon`.  Every bounded cocycle word is `I+O(epsilon)` in normalized HS
norm, while a generic choice is nonidentity on every edge and every relevant
face for all nonzero `epsilon`.  Hence HS defect tends to zero while Hamming
defect stays one.  The cited theorem gives no applicable hypothesis and no
HS correction modulus.
