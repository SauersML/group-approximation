---
rg: 2
id: affine-orientation-glue-lemma
kind: claim
title: Heavy restricted cosets in a positive density of affine directions are hit by a dimension-free bounded set
distinct_from:
  affine-orientation-triangle-defect-is-small: that is the local analytic estimate on triples of affine directions inside one F_2^2 plane; this is the global list-decoding conclusion, and it is what the soundness decoder consumes.
  triangle-defect-globalizes-to-a-bounded-label-list: that is the conditional globalization step (small defect implies a bounded list); this is the unconditional target statement, which needs the defect estimate as well.
artifacts:
  - research/artifacts/unique-games-affine-orientation-2026-08-24.md
---

**OPEN.**  This is the missing analytic ingredient of the
`rich-2to1-games-conjecture` attack on `F_lin` instances.

Fix `Omega = F_2^k`, `N = |Omega|`.  For `b != 0` let

```text
D_b = {X in {-1,1}^Omega : X_x = X_{x+b} for every x},
```

the subcube obtained by identifying the labels in every affine pair
`x + <b> = {x, x+b}`.  A function on `D_b` is a Boolean function whose
coordinates are the cosets `q + <b>`.  Let `f : {-1,1}^Omega -> [-1,1]`,
let `0 < rho < 1` be fixed, and put `g = T_rho f`.  Call a coset `C` of
`<b>` **(d, delta)-heavy** when

```text
Inf^{<=d}_C ( g|_{D_b} ) >= delta.
```

**Statement.**  For every fixed `rho, d, delta, alpha > 0` there exist
constants `L = L(rho, d, delta, alpha)` and `gamma = gamma(rho,d,delta,alpha) > 0`,
**independent of k**, such that: whenever a set `B subset Omega \ {0}` of
density at least `alpha` admits a heavy coset `C_b = q_b + <b>` for every
`b in B`, there is a set

```text
Q subset Omega,   |Q| <= L,
```

with

```text
Pr_{b in B} [ C_b intersect Q != empty ] >= gamma,
```

unless `f` already has one of a bounded number of large ambient low-degree
influences.

The load-bearing words are **independent of k**.  The conclusion is exactly
what the soundness decoder of a Rich 2-to-1 reduction needs: it replaces a
potentially `N`-element list of candidate labels by a bounded one.  Why the
bound cannot be allowed to grow with the alphabet is
`dummy-padding-cannot-beat-the-random-guessing-floor`.

Two things are already known about the shape any proof must have.

* It cannot come from transferring influence from the quotient to the
  ambient cube: `linear-pairing-memorizer-restricts-to-a-dictator` gives a
  bounded, low-degree, noise-*invariant* `f` that restricts to an exact
  dictator on `D_b` while every ambient low-degree influence tends to zero.
  So the escape clause of the statement is not a formality -- the naive
  reading of it is false.
* It cannot come from an `L^2` budget spread over the directions either:
  `affine-memorizers-are-cross-direction-orthogonal` makes all `N-1`
  directions independently addressable inside an ambient `L^2` mass of
  `Theta(N^{1-r})`.

What survives is that any proof must use **bounded range**, **noise
smoothing**, and **higher-order compatibility across directions**
simultaneously.  The compatibility half is isolated as
`affine-orientation-triangle-defect-is-small`.

## Attempts

* **Ambient influence transfer.**  Recorded dead:
  `glue-lemma-via-ambient-influence-transfer`, killed by
  `linear-pairing-memorizer-restricts-to-a-dictator`.  Note the kill is
  robust in a way that is easy to underrate -- the memorizer is homogeneous
  of degree `2r+1`, so `T_rho` multiplies it by the constant `rho^(2r+1)`
  and damps nothing.  Boundedness, low degree and noise *together* still do
  not stop a single direction from being memorized.
* **Parseval budget across directions.**  Recorded dead:
  `glue-lemma-via-parseval-budget-across-directions`, killed by
  `affine-memorizers-are-cross-direction-orthogonal`.
* **Refute it with the memorizer family itself.**  Closed, negatively:
  `memorizer-superposition-has-large-sup-norm` shows every superposition
  `sum_{b in B} c_b B_{b,r}` with `|c_b| >= delta` has sup norm at least
  `delta * |B|^(1/2)`, so no renormalization of the *linear* span of pair
  memorizers is a bounded counterexample, for any sign pattern and any
  positive density of directions.  A counterexample would have to be
  genuinely nonlinear in the memorizers.  That is the sharpest open attack
  currently on the table.
* **Local-to-global via the affine plane.**  The live route
  `glue-lemma-from-small-triangle-defect`: bound the density of
  nonconcurrent `(C_b, C_c, C_{b+c})` triples, then globalize.  Both halves
  are open and are recorded as separate claims, because they fail for
  different reasons.
