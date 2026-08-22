---
rg: 2
id: arithmetic-integral-subgroup-is-incompressible
kind: claim
title: No element of SLn(Q) strictly compresses SLn(Z), so the arithmetic pair is commensurated but never infranormal and Kun-Thom Theorem A cannot reach it
artifacts:
  - research/artifacts/coset-wreath-cartan-entropy-2026-08-22.md
distinct_from:
  finite-infranormal-subgroup-is-normal: that is the elementary fact that finite infranormal subgroups are normal; this is a rigidity theorem for a specific infinite lattice - the compression semigroup of SL_n(Z) in SL_n(Z[1/p]) is trivial - separating the arithmetic lane from the Kun-Thom compression mechanism.
  coordinate-action-not-sofic: that establishes nonsoficity of the coset action for the Kun-Thom infranormal pair; this proves the infranormality hypothesis FAILS for the arithmetic pair, so that theorem and Corollary D are silent about the arithmetic coset action and wreath, whose soficity is genuinely open.
---

Let `n >= 2`, `Lambda = SL_n(Z)`, and let `g` be any element of
`GL_n(Q)` (in particular of `Gamma = SL_n(Z[1/p])`).  Claim (THEOREM):

1. `g Lambda g^{-1} subseteq Lambda` implies `g Lambda g^{-1} =
   Lambda`; the compression semigroup `P_Lambda = {g : g Lambda g^{-1}
   <= Lambda}` equals the normalizer `N(Lambda)`;
2. `N_Gamma(Lambda) = Lambda . Z(Gamma)`; hence `P_Lambda` generates
   only `Lambda . Z(Gamma)`, and `Lambda` is NOT infranormal in
   `Gamma` in the Kun–Thom sense (compression semigroup generates);
3. consequently Kun–Thom Theorem A and Corollary D (arXiv:2608.06222)
   do not apply to the arithmetic pair: the nonsoficity of the coset
   wreath and of the generalized Bernoulli coset action is proved only
   for compression pairs like Theorem E's `EL_r`, and remains OPEN for
   `W_3 = (direct_sum_{Gamma/Lambda} C_2) rtimes SL_3(Z[1/3])`.

Proofs.  (1) Both `Lambda` and `g Lambda g^{-1}` are lattices in
`SL_n(R)`; conjugation preserves Haar measure (unimodularity), so the
two have equal covolume, while containment gives
`covol(g Lambda g^{-1}) = [Lambda : g Lambda g^{-1}] . covol(Lambda)`;
hence the index is `1`.  (2) If `g Lambda g^{-1} = Lambda` then
`g . Z^n` is an `SL_n(Z)`-invariant lattice in `Q^n`.  Invariant
lattices are scalings of `Z^n`: for `v in L`, `e_{ij}(1)v - v` puts
every entry of `v` alone in every coordinate slot, and `L` is a group,
so `(d, 0, ..., 0) in L` for `d` the gcd of all entries of all
elements, giving `L = d Z^n`.  So `q^{-1} g in GL_n(Z)` for some
rational scalar `q`, and `det g = 1` forces `q^n = +-1`, i.e.
`g in GL_n(Z) cap SL_n(Q) . Z = Lambda . Z(Gamma)` up to sign
bookkeeping.  (3) Immediate from the verbatim hypothesis of Theorem A
recorded in `research/artifacts/kun-thom-2608-06222-verified.md`.

**Why this fence matters.**  It proves the arithmetic lane
(commensuration, co-density, Hecke averaging, congruence towers) and
the Kun–Thom lane (strict compression, `E`-normality) are MECHANICALLY
DISJOINT: no route may silently borrow nonsoficity, Corollary D, or
Theorem C fixed-point invariance for the arithmetic wreath `W_3`.  In
particular the hyperlinear side of the p = 3 summit dichotomy
(`nonhyperlinear-coset-wreath-from-p3-collapse`) would NOT
automatically separate hyperlinearity from soficity — `W_3` could a
priori even be sofic; any future claim of `W_3` nonsoficity needs a
new, compression-free argument.  Conversely the entropy ceiling
`coset-wreath-hyperlinearity-forces-strong-one-boundedness` is
unconditional and does not route through Kun–Thom at all.
