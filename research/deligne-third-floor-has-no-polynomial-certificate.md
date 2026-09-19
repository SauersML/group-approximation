---
rg: 2
id: deligne-third-floor-has-no-polynomial-certificate
kind: claim
title: No continuous polynomial phase of any degree on the profinite cochain space separates the Deligne third from the integral subgroup, so every algebraic certificate for the uniform third floor of Sp_4(Z) fails
distinct_from:
  deligne-third-floor-has-no-character-certificate: that kills degree-one certificates (continuous characters, i.e. integral measured cycles) by a Riesz-measure argument; this kills continuous polynomial phases of every degree (quadratic pairings, cubic cup forms, Gowers-type phases), where no measure representation exists, by a new finite-support lemma for integer-valued multilinear forms on C(Omega).
  deligne-schreier-complexes-have-a-uniform-third-cellular-floor: that is the floor itself; this is an obstruction that any proof of it must evade, plus a uniform finite-level version on the congruence tower.
  deligne-monomial-cover-models-have-a-detecting-cycle-floor: that bounds single detecting cycles along towers; this shows that every bounded-degree, bounded-norm polynomial certificate collapses to a detecting cycle on a bounded number of cells, and so dies at every deep congruence level.
---

**ESTABLISHED** (`deligne-third-floor-no-polynomial-certificate-proof`). Unreviewed.

## Setting

Notation of `deligne-third-floor-has-no-character-certificate`:
- `Gamma = Sp_4(Z)`, `Y` its presentation complex, `G` the profinite completion, `Omega = Y^(2) x G`, a compact,
  totally disconnected, metrizable space;
- `E = C^2(Y; C(G,R)) = C(Omega, R)` with the sup norm;
- `L = C(Omega, Z) + delta C^1(Y; C(G,R))`;
- `floor = inf_X mu_(1/3)(X) = dist(kappa/3, L)`.

A **continuous polynomial of degree `<= k`** on `E` is `P(y) = sum_(j<=k) A_j(y, ..., y)`, with each `A_j` a bounded
symmetric `j`-linear form. A **continuous polynomial phase** is a continuous `Q : E -> T` with
`Delta_(h_1) ... Delta_(h_(k+1)) Q = 0` for all `h_i`.

## Statement

1. **Finite-support lemma.** Let `Omega` be compact, totally disconnected and metrizable. Let `A` be a bounded
   `j`-linear form on `C(Omega, R)` with `A(1_(U_1), ..., 1_(U_j)) in (1/N) Z` for all clopen sets `U_i`. Then there is
   a finite `F subset Omega` such that `A(f_1, ..., f_j)` depends only on `f_1|F, ..., f_j|F`.
2. **No polynomial certificate.** Let `P : E -> R` be a continuous polynomial of any degree with `P(L) subset Z`.
   Then `P(kappa/3 + L) subset Z`. The same holds for every continuous polynomial phase `Q : E -> T` with `Q|L = 0`:
   then `Q(kappa/3) = 0`. Degree one is `deligne-third-floor-has-no-character-certificate`, item 2.
3. **Countable-set version.** For every countable `D subset Omega` there are `y_n in kappa/3 + L` with
   `||y_n|| <= 1/2 + 1/n` and `y_n = 0` on an exhausting sequence of finite subsets of `D`. So every `L`-invariant
   function `Phi : E -> R` that is continuous at `0` for bounded convergence pointwise on some countable set has
   `Phi(kappa/3) = Phi(0)`. Such a `Phi` cannot certify the floor. This class contains every `L`-invariant
   cylinder function. It is independent of item 2, because integral polynomials are not `L`-invariant modulo `Z`.
4. **Finite-level shadow (uniform).** For `k >= 1` and `b > 0` there is `R(k, b)` with the following property. Let
   `X` be a finite `Gamma`-set and `P` a polynomial on `C^2(Y_X; R)` of degree `<= k`, with multilinear norms
   `<= b` and `P(L_X) subset Z`. Then `P` depends on at most `R(k, b)` cells. If moreover every ball of radius
   `R(k, b) l_max` in the Schreier complex `Y_X` is isomorphic to a ball in the universal cover, then
   `P(kappa/3) in Z`. Here `l_max` is the longest relator length. This holds on `Gamma / Gamma(N)` for all large
   `N`. So no family of polynomial certificates with bounded degree and bounded norm proves the floor along the
   congruence tower.

## What this changes

- **Class killed.** Item 2 kills every algebraic (finite-degree) certificate on the lamination. This includes:
  - quadratic intersection or Hodge-index pairings;
  - cubic cup-product and Chern-number forms;
  - higher-order Fourier (Gowers-type) phases;
  - any polynomial combination of detecting cycles.
- **Where every member dies.** Each dies at the same two steps:
  - the finite-support lemma (item 1): integrality forces finite point support, via Bonami's inequality for
    Rademacher chaos;
  - leafwise exactness: on the finitely many leaves that meet the support, `kappa/3 = delta(beta/3)` with `beta`
    integral, because each leaf is the universal cover, where `kappa` vanishes on `pi_2`.
- **Named invariant.** The invariant is **finite point support**, or more generally dependence on countably many
  points (item 3).
- **What a proof must use.** A proof of the floor must use a genuinely non-local, sup-norm-over-uncountably-many-leaves
  mechanism, and must be non-polynomial: a min-max or case dichotomy such as (K1)/(K2) of
  `deligne-opnorm-monomial-models-are-almost-flat-circle-bundles`, or a uniform spectral or rigidity argument.
  - `dist(., cl L)` itself is such an invariant: it is `L`-invariant, continuous, and depends on all points.
- **Finite levels.** Item 4 shows that bounded polynomial certificates collapse to bounded detecting cycles, and these
  do not exist at deep levels. So the finite-level form of the kill is uniform in the degree and the norm, not just a
  limit statement.

## Attempts
- **2026-09-19, swarm-0917-w15-w15-deligne-follow: posed and proved.** Item 1 is new. Items 2 and 3 reduce to it
  and to the leafwise exactness of `deligne-third-floor-no-character-certificate-proof`, Step 3. Item 4 is the
  quantitative form, with an explicit `R(k, b)`.
