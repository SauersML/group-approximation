---
rg: 2
id: kazhdan-generators-control-matrix-algebra-distance
kind: claim
title: Near containment of exact Kazhdan generators uniformly controls their entire matrix algebra
distinct_from:
  kazhdan-generator-containment-is-uniform-on-the-group: That controls the group unitaries in arbitrary finite tracial coordinates by a maximum source defect; this controls the entire operator-norm unit ball of the generated coordinate algebra in matrices by the sum of squared source defects.
  full-raw-packet-commutant-witness: That applies commutant Haar averaging to one fixed finite Pauli packet; this combines the averaging identity with a dimension-independent Kazhdan gap for an arbitrary exact representation and an arbitrary target matrix subalgebra.
  kazhdan-rcc-has-prescribed-projective-transfer-slope: That assumes an open global commutant-collapse statement and controls approximate actors; this is unconditional for an exact Kazhdan representation and bounds distance to any matrix subalgebra.
artifacts:
  - research/artifacts/kazhdan-carrier-uniformization-2026-09-08.md
---

Let `C` have a finite Kazhdan generating set `S` with constant `kappa>0`,
using the convention

    max_(s in S)||beta(s)xi-xi|| >= kappa||xi||

for every unitary representation on the complement of its fixed vectors.
Let `sigma:C->U(d)` be an exact representation, put
`A=sigma(C)'' subset M_d`, and let `B subset M_d` be any unital
star-subalgebra. All distances and norms are normalized Hilbert--Schmidt.
Then every `x in A` satisfies

    dist_2(x,B)^2
      <= (4/kappa^2)||x||_op^2
           sum_(s in S)dist_2(sigma(s),B)^2.               (KCU1)

The constant is independent of the dimension, representation,
multiplicities, target algebra, and expression of `x` in the generators.
In particular, for a sequence of such exact representations, pointwise
near containment of the fixed generators implies uniform near containment
of the operator-norm unit ball of the entire coordinate image algebra.
It therefore controls moving congruence slots without a word-length or
level-dependent rate condition.

The theorem requires an exact representation. It does not exactify an
approximate actor or imply flexible Hilbert--Schmidt stability.
