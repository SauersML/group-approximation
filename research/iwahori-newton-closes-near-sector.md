---
rg: 2
id: iwahori-newton-closes-near-sector
kind: claim
title: Uniform infinitesimal rigidity gives a linear defect-to-distance bound within a fixed neighbourhood of the compatible locus
artifacts:
  - research/artifacts/hs-dehn-modulus-length-control-2026-08-20.md
distinct_from:
  iwahori-uniform-infinitesimal-rigidity: that is the first-order (cocycle) gap at compatible points; this integrates it to a genuine local distance bound on the nonlinear representation variety by Newton--Kantorovich, with an explicit neighbourhood radius.
---

Let `Lambda = SL_2(Z) * SL_2(Z)`, `pi = (pi_+, pi_-) in X_FD(Lambda)` a pair
of `d`-dimensional unitary representations, `def(pi) = max_(s in S_B)
||pi_+(s) - pi_-(sigma s)||_2` the Iwahori defect, and `D(pi) = inf` of
`d_2(pi, pi~)` over compatible `pi~` (those with an exact common Iwahori
restriction, i.e. genuine representations of `SL_2(Z[1/2])`).  Let
`sigma_0 > 0` be the uniform infinitesimal-rigidity constant of
`iwahori-uniform-infinitesimal-rigidity` (the smallest nonzero singular
value of the Mayer--Vietoris mismatch map in the cochain norm, uniform over
congruence `rho` and dimension).

**Theorem.**  There are constants `L` (dimension-free, from the fixed
relator words) and `r_0 = sigma_0^2/(8L) > 0` such that: if `pi` is within
`r_0` of the compatible locus `C = X_FD(SL_2(Z[1/2]))`, i.e. `D(pi) < r_0`,
then

```text
D(pi) <= (2/sigma_0) def(pi).                                          (NR1)
```

Equivalently, the modulus `f` in Dogon--Vigdorovich's question can be taken
linear, `f(x) = (2/sigma_0) x`, on the tube of radius `r_0` around `C`.

*Proof.*  Let `pi~ in C` realize `D(pi) = d_2(pi, pi~) < r_0`.  Consider the
"compatibility map" `F(rho) = (pi_+ rho|_B - pi_- rho|_B o sigma)` valued in
`prod_(s in S_B) M_d`, defined on the smooth manifold of pairs of
representations of `SL_2(Z)` near `pi~` (a product of two copies of the
representation variety of `SL_2(Z) = Z/4 *_{Z/2} Z/6`, smooth near `pi~`
because the eigenvalue multiplicities of the torsion generators are locally
constant, so the local model is a product of two conjugation orbits).  Its
differential at `pi~` is exactly the Mayer--Vietoris mismatch map on
`Z^1(SL_2(Z), Ad pi~_+) (+) Z^1(SL_2(Z), Ad pi~_-)` modulo the diagonal
coboundaries; by `iwahori-uniform-infinitesimal-rigidity` it has a right
inverse of norm `<= 1/sigma_0` transverse to the conjugation orbit, uniform
in `d`.  Each component of `F` is a fixed word of length `<= 6` in unitaries
of operator norm one, so `||D^2 F|| <= L` with `L` a fixed constant (second
finite differences of a length-`k` word are bounded by `k^2` in normalized
HS).  Newton--Kantorovich: with `beta = 1/sigma_0`, residual
`eta = ||DF(pi~)^+ F(pi)||` and `||F(pi)|| = def(pi)`, the condition
`beta L (beta def(pi)) <= 1/2` holds because `def(pi) <= (1 + L) D(pi) <
(1+L) r_0 <= sigma_0^2/(4L) beta^(-1)` for `r_0` as stated, and the
iteration started at `pi` converges to a zero `pi^* in C` with
`d_2(pi, pi^*) <= 2 beta def(pi) = (2/sigma_0) def(pi)`.  Since `pi^*` is
compatible, `D(pi) <= d_2(pi, pi^*)`. ∎

**What this closes and what it does not.**  It makes the near sector of
`iwahori-local-global-defect-question` a theorem with an explicit tube
radius.  It says nothing about representations of Iwahori-defect below
`sigma_0 r_0` that are farther than `r_0` from every compatible
representation; those are the far sector, `iwahori-outlier-repair`, and the
only place the mismatch map's uniform gap is not available is exactly there
(at a non-compatible `pi` the differential `DF(pi)` need not be the
Mayer--Vietoris map of a congruence local system, so infinitesimal rigidity
does not apply).  The dichotomy "near or far" is therefore complete once
the far sector is controlled.

## Attempts

- The dimension-free right inverse is the content of
  `iwahori-uniform-infinitesimal-rigidity`; without it Newton's `beta`
  would grow with `d` and the tube radius would shrink to zero.
- The smoothness of `X_FD(SL_2(Z))` near `pi~` uses that torsion-generator
  eigenvalue multiplicities are locally constant; at points where they
  collide the variety is singular, but `pi~` congruence has generic
  multiplicities, and a general nearby `pi` can be conjugated into the same
  stratum without increasing `def` by more than `O(D(pi))`.
- The far sector genuinely needs a different tool: a low-defect `pi` far
  from `C` would have `pi_+` and `pi_-` two representations of `SL_2(Z)`
  agreeing to within `def` on the index-three Iwahori subgroup yet not
  extending to a common `SL_2(Z[1/2])`-representation even approximately;
  ruling this out is `iwahori-outlier-repair` and its localization lane.
