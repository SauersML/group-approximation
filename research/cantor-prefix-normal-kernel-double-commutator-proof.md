---
rg: 2
id: cantor-prefix-normal-kernel-double-commutator-proof
kind: route
title: Displace a cylinder and extract a nontrivial prefix commutator from the normal kernel
target: cantor-prefix-subgroup-detects-every-normal-kernel
requires: []
artifacts:
  - research/artifacts/boone-higman-wreath-projection-audit-2026-09-08.md
---

Write [a,b]=a*b*a^-1*b^-1 and compose functions from right to left.
Choose 1!=f in N. Since E acts faithfully, some point p is moved by f.
Choose disjoint neighborhoods of p and f(p), and then a nonempty
cylinder U around p small enough that U and f(U) are disjoint. This
uses only continuity and the cylinder basis of the Cantor topology.

Choose three distinct subcylinders U_1,U_2,U_3 inside U at a common
sufficiently deep level. Let a be the prefix permutation interchanging
U_1,U_2, and let b interchange U_2,U_3; both fix everything else.
Then a,b belong to V_m, are supported in U, and [a,b]!=1: on these
three subcylinders their commutator is a nontrivial 3-cycle.

Put c=f*a^-1*f^-1. It is supported in f(U), so c commutes with b.
Since [a,f]=a*c, direct multiplication gives

    [[a,f],b] = a*c*b*c^-1*a^-1*b^-1
              = a*b*a^-1*b^-1
              = [a,b].

Normality and f in N give [a,f] in N, hence [[a,f],b] in N. Thus
1!=[a,b] belongs to N intersect V_m, as claimed.

For a homomorphism Phi:E->Q injective on V_m, its normal kernel has
trivial intersection with V_m. The preceding result forces that kernel
to be trivial. A localized coefficient L_v(h), with h a nonidentity
homeomorphism and v a nonempty word, is nonidentity because it acts as
h on the suffix of the cylinder v*C_m. Therefore it cannot be killed
by such a Phi.

This is the standard displacement/double-commutator argument, written
out here for the precise kernel test being used. No novelty is claimed.
It is a mathematical proof, not a Lean certificate.
