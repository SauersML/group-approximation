---
rg: 2
id: affine-orientation-glue-lemma
kind: claim
title: Heavy restricted cosets in a positive density of affine directions are hit by a dimension-free bounded set
distinct_from:
  affine-orientation-triangle-defect-is-small: that is the local analytic estimate on triples of affine directions inside one F_2^2 plane; this is the global list-decoding conclusion, and it is what the soundness decoder consumes.
  triangle-defect-globalizes-to-a-bounded-label-list: that is the conditional globalization step (small defect implies a bounded list); this is the unconditional target statement, which needs the defect estimate as well.
  glue-lemma-holds-for-quadratic-functions: that is the proved special case at ambient degree two, where the conclusion holds with gamma = 1 and no density hypothesis; this is the open general statement for arbitrary bounded f.
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
Pr_{b in B} [ C_b intersect Q != empty ] >= gamma.
```

The load-bearing words are **independent of k**.  The conclusion is exactly
what the soundness decoder of a Rich 2-to-1 reduction needs: it replaces a
potentially `N`-element list of candidate labels by a bounded one.  Why the
bound cannot be allowed to grow with the alphabet is
`dummy-padding-cannot-beat-the-random-guessing-floor`.

**Note on the escape clause (2026-08-24).**  The statement was handed over
with a trailing "unless `f` already has one of a bounded number of large
ambient low-degree influences".  That clause has been **deleted**, and the
deletion is a correction rather than a strengthening for its own sake: by
`glue-lemma-escape-clause-voids-the-conclusion`, replacing `f` by
`(X_z + f)/2` preserves the range, preserves every heavy coset, and buys a
large ambient influence at `z`, so an adversary switches the clause on for
the price of one coordinate and the statement then asserts nothing.  In the
form above, ambient influential coordinates reappear where they belong --
as one admissible choice of `Q`, which is exactly how the proved case
`glue-lemma-holds-for-quadratic-functions` produces them.

**What is known about the shape of any proof.**

* **Ambient degree two is done, and it is sharp.**
  `glue-lemma-holds-for-quadratic-functions` proves the conclusion for
  `deg f <= 2` with `L = 16/delta`, `gamma = 1`, no density hypothesis and
  no dependence on `rho, d, k`.  The list is the set of ambient influential
  coordinates.  By `restricted-influence-transfer-holds-below-degree-three`
  that argument is exactly as strong as it can be: the transfer inequality
  it rests on holds iff no full coset can be absorbed into a Fourier set,
  which happens iff `deg <= 2`, and it is **false** at degree three with the
  memorizer as witness.  So the obstruction is the *ambient* degree, not
  `d` and not `rho`.
* **It cannot come from ambient influence transfer in general.**
  `linear-pairing-memorizer-restricts-to-a-dictator` gives a bounded,
  low-degree, noise-*invariant* `f` that restricts to an exact dictator on
  `D_b` while every ambient low-degree influence tends to zero.
* **It cannot come from counting the heavy directions.**  By
  `dictator-is-heavy-in-every-affine-direction`, `f = X_p` is heavy in all
  `N-1` directions at level `rho^2` while spending one unit of `L^2`.  The
  content is never scarcity of heavy directions -- it is **concentration of
  their centres**.
* **It cannot come from an `L^2` budget spread over the directions.**
  `affine-memorizers-are-cross-direction-orthogonal` makes all `N-1`
  directions independently addressable inside ambient `L^2` mass
  `Theta(N^(1-r))`.

What survives is that any proof must use **bounded range**, **noise
smoothing**, and **higher-order compatibility across directions**
simultaneously, and by
`restricted-influence-transfer-holds-below-degree-three` it must act on the
tail of

```text
hat{g|_{D_b}}({C}) = [ hat g(q) + hat g(q+b) ]
                     + sum_{m>=1} sum_{R a union of m cosets disjoint from C}
                         [ hat g({q} union R) + hat g({q+b} union R) ],
```

since the leading bracket is precisely the part the degree-two argument
already controls.  The compatibility half is isolated as
`affine-orientation-triangle-defect-is-small`.

## Attempts

* **Ambient influence transfer.**  Recorded dead in general:
  `glue-lemma-via-ambient-influence-transfer`, killed by
  `linear-pairing-memorizer-restricts-to-a-dictator`.  The kill is robust in
  a way that is easy to underrate -- the memorizer is homogeneous of degree
  `2r+1`, so `T_rho` multiplies it by the constant `rho^(2r+1)` and damps
  nothing.  Boundedness, low degree and noise *together* still do not stop a
  single direction from being memorized.  **But the route is not dead
  below degree three**, and
  `restricted-influence-transfer-holds-below-degree-three` says exactly
  where it stops.
* **Parseval budget across directions.**  Recorded dead:
  `glue-lemma-via-parseval-budget-across-directions`, killed twice over --
  by `affine-memorizers-are-cross-direction-orthogonal` and, more cheaply,
  by `dictator-is-heavy-in-every-affine-direction`.
* **Refute it with the memorizer family itself.**  Closed, negatively:
  `memorizer-superposition-has-large-sup-norm` shows every superposition
  `sum_{b in B} c_b B_{b,r}` with `|c_b| >= delta` has sup norm at least
  `delta * |B|^(1/2)`, so no renormalization of the *linear* span of pair
  memorizers is a bounded counterexample, for any sign pattern and any
  positive density of directions.  A counterexample would have to be
  genuinely nonlinear in the memorizers.
* **Induct on ambient degree.**  The obvious next move after the degree-two
  case.  Where it dies: the fibre `{S : pi_b(S) = T}` grows like `N^m` with
  the number `m` of absorbed cosets, and the memorizer shows the fibre sum
  can be fully coherent, so a Cauchy--Schwarz over the fibre loses
  everything at the first step and there is no induction hypothesis on
  `deg <= D` that survives to `D+1` by counting alone.
* **Local-to-global via affine stars.**  The live route
  `glue-lemma-from-small-triangle-defect`: bound the product-uniform density
  of pairs without a concurrency certificate, then globalize.  The
  globalization half is now established, sharply, by
  `triangle-defect-globalizes-to-a-bounded-label-list`: a maximum
  star-degree affine pair is itself a two-label hitting set.  The analytic
  star-density estimate remains open and is the only unresolved premise of
  this route.
