---
rg: 2
id: km-246-lattice-fp-simple-kazhdan-irs-rigid-for-q-ge-4-citation
kind: route
title: Import Caprace-Thom Proposition 4.1 and Corollary 5.3 and Caprace-Remy Theorem 20 and Corollary 21 at type (2,4,6)
target: km-246-lattice-fp-simple-kazhdan-irs-rigid-for-q-ge-4
requires: []
---

Both PDFs were read on 2026-09-13 from arXiv on MSI.

**Caprace--Thom, *On the Howe--Moore property for automorphism groups of buildings*,
arXiv:2606.27993v2 (17 Jul 2026).**
- *Proposition 4.1(1)* (p. 10): "Let `X` be a thick locally finite building of finite rank
  whose Weyl group is of compact hyperbolic type `D = (m_1,...,m_r)`, and let
  `G < Aut(X)` be a closed type-preserving subgroup acting Weyl-transitively. Suppose that
  one of the following conditions holds: (1) `D ∈ {(2,4,6), (3,3,4), (3,3,3,4),
  (3,3,3,3,4)}` and `q_min >= 3`. [...] Then `G` has Kazhdan's property (T)." Here
  `q_s + 1` is the number of chambers on an `s`-panel.
- *Corollary 5.3* (p. 14): "Let `Λ` be a minimal simply connected split Kac--Moody group
  over a finite field of order `q`, and `Z` be its center. Suppose that the Weyl group `W`
  of `Λ` is of compact hyperbolic type `D = (m_1,...,m_r)`. Suppose that `q = q_min`
  satisfies one of the conditions (1)--(7) of Proposition 4.1. Then every invariant random
  subgroup of `Λ/Z` is a convex combination of the trivial ones, namely `δ_e` and `δ_(Λ/Z)`."
- *Proof of Corollary 5.3* (p. 14): `Λ/Z` is an irreducible lattice in `L_+ x L_-`, the
  closures of its images in the automorphism groups of the two buildings, for all `q >= 2`
  by their Lemma 5.1; `L_+` and `L_-` have (T) by Proposition 4.1. A lattice in a Kazhdan
  locally compact group is Kazhdan (Bekka--de la Harpe--Valette, Theorem 1.7.1), so `Λ/Z`
  has (T).
- The abstract states the outcome: "examples of infinite finitely presented Kazhdan groups
  with exactly two ergodic invariant random subgroups".

**Caprace--Remy, *Simplicity and superrigidity of twin building lattices*,
arXiv:math/0607664v2.**
- *Theorem 20* (p. 24): "Let `Λ` be a split or almost split Kac--Moody group over a finite
  field `F_q` of order `q`. [...] Assume that `(W,S)` is irreducible, neither of spherical
  nor of affine type and that `W(1/q) < +∞`. Then the derived group of `Λ`, divided by its
  center, is simple." The same page: "if `q > 3` then every rank one subgroup of the
  Kac--Moody group `Λ` is perfect", and for the simply connected root datum
  "`Λ = Λ† = [Λ,Λ]` (if `q > 3`)". Caprace--Thom's Lemma 5.1 gives `W(1/q) < ∞` for
  `q >= 2`.
- *Corollary 21* and its proof (p. 25): "Finite presentation follows from [AM97] under the
  hypothesis that `q_min > 2`", for twin root data satisfying (S0), (S1), (S2), (S3+) of
  their Theorem 19 in which any two canonical reflections generate a finite group. [AM97]
  is Abramenko--Muhlherr, C. R. Acad. Sci. Paris 325 (1997); it was not read here.

**Assembly at type `(2,4,6)`, `q >= 4`.**
- The type is compact hyperbolic and 2-spherical: the rank-two orders are `2, 4, 6`, all
  proper subdiagrams are spherical, and `1/2 + 1/4 + 1/6 < 1`.
- Thickness is `q + 1 >= 5`, so `q_min = q >= 3`, and Proposition 4.1(1) and Corollary 5.3
  apply.
- Since `q > 3`, `Λ = [Λ,Λ]` and Theorem 20 makes `Λ/Z` simple. It is infinite because `W`
  is.
- (S0)--(S3+) hold for split Kac--Moody groups over `F_q` with `q > 3`, as Caprace--Remy
  check on p. 24. With `q_min > 2`, Corollary 21's proof gives finite presentation of `Λ`.
  A quotient of a finitely presented group by a finite normal subgroup is finitely presented.
