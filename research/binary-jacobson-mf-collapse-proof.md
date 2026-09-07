---
rg: 2
id: binary-jacobson-mf-collapse-proof
kind: route
title: Put the Jacobson head in a locally finite ideal and apply Kazhdan orbit rigidity
target: binary-jacobson-steinberg-head-root-is-mf-invisible
requires:
  - semisimple-packet-multiplicity-collapse
  - binary-jacobson-steinberg-cover-is-elementary
artifacts:
  - research/artifacts/locally-finite-dimensional-compression-2026-09-07.md
  - non_mf_groups_exist.tex
---

Work first in EL_4(J), where J=F_2<S,T | TS=1> and Q=1-ST.
The ideal JQJ is spanned by the matrix units S^i Q T^j and is the
union of finite matrix rings. Consequently the congruence kernel
EL_4(J) intersect (1+M_4(JQJ)) is locally finite and normal.

Let L=EL_3(J) on the first three coordinates. It has property (T)
by Ershov--Jaikin-Zapirain, Theorem 1.1. The rank-four compression
cell in the linked proof, using only TS=1, gives

    u L u^-1 <= L,       c in C(L),
    b = u c u^-1 = e_12(Q),
    [b,e_23(1)] = e_13(Q) != 1.

The L-orbit of b lies in the locally finite congruence kernel.
Every finite orbit window therefore has finite-dimensional group
C-star algebra. The semisimple-packet collapse kills [b,e_23(1)]
in every norm-corona representation.

Restricting a representation of EL_5(J) to the rank-four block
proves invisibility of its head root. The established isomorphism
St_5(J) ~= EL_5(J) transfers this to the target Steinberg group.
The artifact also proves directly that the entire finitary symbol
kernel, and exactly that kernel, is its MF radical.

The proof uses property (T) of the compressed EL_3(J). It does not
require property (T) of the locally finite kernel or fullness of Q.
The new endpoint is a paper proof, not a new Lean certificate.
