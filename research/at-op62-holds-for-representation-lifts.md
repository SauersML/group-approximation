---
rg: 2
id: at-op62-holds-for-representation-lifts
kind: claim
title: Alekseev-Thom Open Problem 6.2 holds when the coordinate lifts are genuine representations
distinct_from:
  wall-coordinate-reduction-under-at-op62: that proves the conditional reduction "OP 6.2 implies the wall becomes a finite-dimensional nested-centralizer demand" and explicitly does not assert the hypothesis; this establishes the hypothesis on the representation-lift sector and locates the remaining open content in the inexact lifts.
  kazhdan-almost-invariant-corner-near-invariant-projection: that is the general corner lemma with its ultraproduct corollary; this is its instantiation at the Alekseev-Thom interface, recording what it does and does not give for Open Problem 6.2.
  kt-centralizer-normalization-hs: that asks whether the relative commutant is NORMALIZED by the ambient group image, the Kun-Thom Theorem 4.1 analogue; this concerns the coordinate STRUCTURE of the commutant itself, with no normalization statement.
---

**THEOREM.**  Let `Gamma` be a finitely generated Kazhdan group,
`rho_n : Gamma -> U(d_n)` genuine finite-dimensional unitary
representations, `M = prod_U M_(d_n)` the tracial ultraproduct and
`pi = [rho_n]`.  Then

```text
pi(Gamma)' cap M  =  prod_U ( rho_n(Gamma)' cap M_(d_n) ),          (OP1)
```

the ultraproduct of the coordinate centralizers.  This is the
representation-lift instance of Alekseev--Thom arXiv:2608.05362 Open
Problem 6.2 (whether the commutant of a Kazhdan representation into a
tracial matrix ultraproduct is the ultraproduct of the coordinate
centralizers of lifts), in the normalized-HS category; it is the exact
analogue of their theorem that the centralizer of a sofic embedding of a
Kazhdan group is a metric ultraproduct of permutation centralizers.

**Where the open content of OP 6.2 now sits.**  For an arbitrary
hyperlinear representation the coordinate lifts `u_n` are only
almost-multiplicative, `Ad u_n` is not a representation, and property (T)
has nothing to average against; moreover the exact centralizer
`{x : [x, u_n(gamma)] = 0}` is not stable under HS-small perturbation of
the coordinates `u_n`, so `(OP1)` does not transport along a flexible
correction of the microstates even where one exists.  The problem is
therefore open exactly on the everywhere-inexact sector — the same
habitat as `sl3z-regular-microstates-are-congruence-correctable` and the
outlier complement of `subgroup-exact-outliers-do-not-exist`.  Through
`wall-coordinate-reduction-under-at-op62`, on any wall model whose
windows are realized by genuine representations the wall is already a
finite-dimensional nested-centralizer demand `lim_omega
[tilde A_n : A_n] > 1` with no further hypothesis.
