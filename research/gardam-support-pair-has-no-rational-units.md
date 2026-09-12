---
rg: 2
id: gardam-support-pair-has-no-rational-units
kind: claim
title: A characteristic-zero field supports a nontrivial unit on Gardam's 21-element pair only if it contains zeta_8
distinct_from:
  unit-conjecture-fails-over-complex-numbers: that imports the existence of nontrivial complex units on this support pair; this determines which characteristic-zero fields admit them and excludes Q, R and Q_2.
  promislow-radius4-one-sided-and-integral-separation: that is a one-sided radius-four census over F_2 whose integral part covers only nontrivial residues; this fixes both supports to Gardam's pair and covers every residue.
  rational-unit-conjecture-torsion-free: that is the unit conjecture over Q for every torsion-free group; this is one fixed support pair on one group.
  rational-units-rescale-to-integral-units: that transfers units between Q and Z on one group; this is a finite classification on one support pair.
---

**ESTABLISHED.** Let `S` and `T` be the 21-element subsets of the Promislow
group `P` that support Gardam's unit and its inverse (arXiv:2312.05240,
Theorem A, ordered as in the zenodo script `unit_problem.py`). Let `K` be a
field of characteristic zero, and let `u in K[P]` be a unit with
`supp(u) in S` and `supp(u^(-1)) in T`. If `u` is not `lambda g`, then `K`
contains a primitive eighth root of unity.

So no nontrivial unit of `Q[P]`, `R[P]`, `Q_2[P]` or `Z[P]` has support in
`S` and inverse support in `T`. Conversely, every field containing `zeta_8`
has one, by specializing Gardam's unit.

Over `Qbar` there are exactly 16 nontrivial units on this pair up to scaling,
and each is a reduced isolated point of the solution variety. These are
Gardam's 16. This removes the "bad prime" caveat of Gardam's Section 3, where
the classification was computed modulo `1000000007`.

This is one support pair. It does not bound the support of a unit of `Z[P]`
or `Q[P]` in general, and it says nothing about other supports at word radius
four or five.

DERIVATION
[[gardam-support-pair-has-no-rational-units-proof]]
