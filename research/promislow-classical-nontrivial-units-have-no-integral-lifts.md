---
rg: 2
id: promislow-classical-nontrivial-units-have-no-integral-lifts
kind: claim
title: No unit of Z[P] reduces to Gardam's unit, to a radius-four census unit, or to a Murray unit for d = 3, 5, 7
distinct_from:
  promislow-radius4-one-sided-and-integral-separation: that shows a unit of Z[P] supported in B(4) has trivial residue modulo 2; this excludes the same 52 residues for integral units of every support and height.
  gardam-support-pair-has-no-rational-units: that excludes rational units with support and inverse support fixed to Gardam's pair; this excludes every integral unit whose residue modulo 2 is Gardam's unit, with no support condition.
  murray-z-only-shape-has-no-char0-units-any-inverse: that excludes characteristic-zero units of Murray's shape; this excludes integral units of any shape whose residue modulo d is a Murray unit.
  integral-unit-conjecture-torsion-free: that is Higman's conjecture for every torsion-free group; this removes only the Case B lifts of the known nontrivial residues on P.
artifacts:
  - research/artifacts/promislow-definite-line-shadows-2026-09-13.md
---

**ESTABLISHED.** Let `P` be the Promislow group. No unit of `Z[P]` reduces

1. modulo 2 to Gardam's unit of `F_2[P]`, the reduction of the unit in
   `unit-conjecture-fails-over-complex-numbers` (every coefficient of that unit
   is a signed monomial `+-s^i t^j`, so the residue is the sum of the 21
   elements of its support);
2. modulo 2 to any of the 52 nontrivial units of `F_2[P]` supported in `B(4)`
   (`promislow-radius4-one-sided-and-integral-separation`);
3. modulo `d` to a unit of Murray's Theorem 3 (arXiv:2106.02147, as transcribed
   in `murray-z-only-ansatz-has-no-char0-units`), for `d in {3, 5, 7}` and each
   of the eight parameter pairs `(t_M, w)` with `t_M in {-1, 0, 1, 2}` and
   `w in {0, 1}`.

No condition is placed on the support, word radius or coefficient height of the
integral unit.

**Mechanism.** Each of these residues maps to an element of norm `1` that is
not a monomial under shadows A and B of
`promislow-integral-units-have-monomial-definite-line-shadows`, and item 4 of
that claim applies. Under shadow C all of them are monomials. Exact results
(log in the artifact):

| residues                      | count            | non-monomial shadows |
|-------------------------------|------------------|----------------------|
| Gardam's unit, `d = 2`        | 1                | A, B                 |
| radius-four census, `d = 2`   | 52, in 7 orbits  | A, B for every unit  |
| Murray, `d = 3, 5, 7`         | 24               | A, B for every case  |

For Gardam's unit, shadow A is `t^-2 + 1 + t^2 + (t^-2 + t^2) u` over `F_2`.

**Relation to Case B.** Tabei (arXiv:2608.02982v1, Proposition 3.1) splits
Higman's conjecture for `P` into Case A, units with trivial residue modulo 2,
and Case B, units with nontrivial residue. Main previously excluded the 52
census residues only for integral units supported in `B(4)`. For these residues
Case B is now closed at every radius. Case A is untouched, and so is every
nontrivial residue whose shadows on all three definite lines are monomials.

**Scope.** These are finitely many named residues. Another nontrivial unit of
`F_d[P]` is excluded as a residue once one of its shadows is computed and is not
a monomial. No novelty is claimed.

DERIVATION
[[promislow-classical-residues-shadow-computation]]
