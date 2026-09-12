---
rg: 2
id: matrix-unit-root-rank-models-of-odd-char-simple-el3-are-trivial
kind: claim
title: In odd characteristic a rank model of EL_3 over a simple non-directly-finite ring is trivial once its unit root elements act by matrix units
distinct_from:
  matrix-unit-root-rank-models-of-simple-el3-are-trivial: that is the characteristic-two statement, proved by five-term commutator expansions of square-zero root actions; this is odd characteristic, where root actions only satisfy n^p = 0 and the diagonal torus of SL_3(F_p) replaces the expansions.
  block-unipotent-rank-models-of-leavitt-el3-are-trivial: that assumes block support of every root element x_ij(a), for all a in R; this assumes block support only of the six unit root elements and derives the rest.
  el3-rank-models-factor-through-ring-rank-models: that is the open claim that every rank model extracts a ring rank model; this is the established odd-characteristic case where the unit root elements act by matrix units with trivial complement.
artifacts:
  - research/artifacts/el3-rank-ring-rigidity-2026-09-12.md
---

**ESTABLISHED** (proof in the artifact, Section 4d, Proposition 8 and Corollary 9;
independent verification requested from `gk-vf-linear`). Let `p` be odd and `R` a simple
algebra of characteristic `p` that is not directly finite, for instance `L_K(1,n)` with
`char K = p` and `n >= 2`. Let `M` be a rank ultraproduct over a field of characteristic `p`,
and `sigma : EL_3(R) -> M^x` a homomorphism. Suppose there are pairwise orthogonal
idempotents `p_1, p_2, p_3` with

```text
sigma(x_ij(1)) = 1 + u_ij,   u_ij in p_i M p_j,   u_ij u_jk = u_ik,   u_ij u_ji = p_i .
```

Then `sigma` is trivial.

- **Propagation.** Commutation with `u_12` and `u_23` puts `n_13(a)` in block form. The torus
  elements `diag(-1,-1,1)` and `diag(1,-1,-1)` of `SL_3(F_p)` invert `x_13(a)`, and together
  with `n^p = 0` and the invertibility of `2` they kill every entry outside `p_1 M p_3`. Weyl
  elements transport this to all roots.
- **Collapse.** The coefficients form a unital ring homomorphism into a directly finite corner,
  and simplicity together with `ts = 1 != st` kills it.

**For the `F_3` gate.** `EL_3(L_(F_3)(1,2)) <= L_(F_3)(1,2)^x`, and that unit group embeds in
`PG`. So an `F_3`-linear sofic approximation of either group restricts to `SL_3(F_3)` as
something other than `(natural (x) W) (+) trivial`. That excludes the degree-truncation and
hybrid constructions from `projective-ternary-group-is-f3-linear-sofic`.
