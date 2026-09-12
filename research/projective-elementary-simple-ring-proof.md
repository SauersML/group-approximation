---
rg: 2
id: projective-elementary-simple-ring-proof
kind: route
title: Use a proper ideal to produce a noncentral congruence kernel and a nonabelian elementary quotient
target: projective-elementary-simplicity-forces-simple-ring
requires: []
artifacts:
  - research/artifacts/boone-higman-projective-finiteness-gate-2026-09-08.md
---

Write E=EL_n(R), Z=Z(E), and suppose I is a nonzero proper two-sided
ideal of R. Reduction gives a surjection E -> EL_n(R/I): every elementary
generator downstairs has a lift. Write C for its normal kernel.

For 0!=a in I, e_12(a) belongs to C and is not central in E, since

    [e_12(a),e_23(1)] = e_13(a) != 1.

Hence CZ/Z is a nontrivial normal subgroup of E/Z. If E/Z is simple,
then CZ=E. It follows that EL_n(R/I), the image of E, is the image of Z
and is therefore abelian.

But EL_n(R/I) is perfect: for distinct i,j,k,

    e_ij(b) = [e_ik(b),e_kj(1)].

It is also nontrivial, since R/I is a nonzero unital ring and e_12(1)!=1.
A nontrivial perfect group cannot be abelian. This contradiction rules
out every nonzero proper ideal I. Therefore R is simple.

