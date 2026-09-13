---
rg: 2
id: kt-hyperlinear-coset-wreath-forces-nonroundable-vertex
kind: claim
title: A hyperlinear intermediate Kun--Thom coset wreath yields a model of the actor whose polynomial vertex does not flexibly round
distinct_from:
  hs-stable-vertex-rounding-for-every-model: that is the open hypothesis (H1) for every model and every infranormal Kazhdan pair; this proves that a hyperlinear intermediate wreath over the Theorem E pair produces one explicit trace-preserving model at which (H1) fails.
  theorem-e-vertex-rounds-to-unit-type-representations: that is the open universal unit-type rounding statement; this is the proved per-model contrapositive of its route, extended from the base wreath to every intermediate coset wreath and to the double.
  kt-canonical-hs-normalization-fails: that is the open existence of a Connes-embeddable non-normalized model; this shows that every trace-preserving model extracted from a hyperlinear intermediate wreath has a non-roundable vertex restriction.
  sl2-half-stability-excludes-hnn-hyperlinearity: that is the same stability-versus-hyperlinearity fork for the arithmetic pair SL2(Z) < SL2(Z[1/2]) and its centralizer HNN group, through the tau gap and co-density; this is the fork for the Kun--Thom Theorem E pair, through the unit-type rounding chain, for every intermediate coset wreath and the double.
---

**ESTABLISHED.** Let `Gamma = EL_r(F_q[x_1..x_d]) < G = EL_r(F_q[x^(+-1)]) rtimes SL_d(Z)`,
`r, d >= 3`, be the Kun--Thom Theorem E pair, `N = <<Gamma>>_G`, and `F_Gamma` a finite
generating set of `Gamma`. Let `Gamma <= K <= G` with `N` not contained in `K`, and put
`W_K = (direct_sum_(G/K) Z/2) rtimes G`.

If `W_K` is hyperlinear, then there is a trace-preserving homomorphism
`sigma : G -> U(prod_U M_n)` such that:
1. `sigma(G)` does not normalize `R = sigma(Gamma)' cap prod_U M_n`;
2. (H1) fails at `sigma`: after any `o(n)` padding, no genuine representations
   `pi_n : Gamma -> U(n')` with `n'/n -> 1` satisfy
   `max_(s in F_Gamma) ||sigma_n(s) - pi_n(s)||_2 -> 0` along `U`.

In particular `Gamma` is not flexibly Hilbert--Schmidt stable. The same conclusion follows
if the double `G *_Gamma G` is hyperlinear, since that is equivalent to hyperlinearity of
`W_Gamma` (`kt-wreath-hyperlinear-iff-double-hyperlinear`), and `K = Gamma` qualifies.

**Reading.**
- Every route to Question 3.4 through a Kun--Thom coset wreath or double already contains a
  flexible normalized-HS instability theorem for the residually finite Kazhdan group
  `EL_r(F_q[x_1..x_d])`, at models that extend to the actor. That would be new in kind.
  - Dogon (arXiv:2211.10492v3, p. 3, quoted in
    `research/artifacts/hs-flexible-versus-strict-stability-2026-09-12.md`) records that
    finitely generated hyperlinear groups that are not residually finite are never flexibly
    stable.
  - The residually finite unstable examples listed there, `SL_2(Z) rtimes Z^2` and
    `F_m x F_k`, are not Kazhdan.
  - Flexible stability of infinite Kazhdan groups is recorded there as undecided.
- Contrapositively, flexible stability of `Gamma` at `G`-extendable models makes every
  intermediate coset wreath `W_K` non-hyperlinear, not only `W_Gamma`.
- The implication is conditional on nothing beyond its four established premises. It does
  not reduce the logical strength of either branch: it names what each branch must contain.

Derivation: `kt-hyperlinear-coset-wreath-forces-nonroundable-vertex-proof`.
