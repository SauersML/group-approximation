---
rg: 2
id: smoothing-normal-subgroup-cantor-dichotomy-proof
kind: route
title: Steps 2-4 of the cyclic argument use only the smoothing hypothesis, and for finite groups orbit sums classify equidecomposability by induction on the stabilizer
target: smoothing-normal-subgroup-cantor-dichotomy
requires: [coinvariant-tarski-lemma-minimal-nowhere-scattered, rainone-type-semigroup-crossed-product-dichotomy, minimal-normal-cyclic-subgroup-cantor-dichotomy]
---

**Parts 1--3 under (SM).**  Steps 2, 3 and 4 of
`minimal-normal-cyclic-subgroup-cantor-dichotomy-proof` use only (SM):

* normality, for the action of `Gamma / H` on `K^0(X, H)`;
* cancellation of `S(X, H)`, for lifting in the coinvariants-in-stages step;
* (R), (P) and (ND) for `K^0(X, H)`, where (ND) comes from simplicity (by
  minimality of `H`) and noncyclicity;
* minimality of `Gamma`, which follows from minimality of `H`.

Part (a) of (SM) is part 1 of `minimal-normal-cyclic-subgroup-cantor-dichotomy`.

**Part (b), Step A: finite groups.**  Let a finite group `F` act on a compact
totally disconnected metrizable space `Y`.  For `f in C(Y, Z)` put
`phi_f(y) = sum_(z in F y) f(z)`, summing over the orbit as a set.

*Claim: for `f, g in C(Y, N)`, `f ~_F g` iff `phi_f = phi_g`.*  Moving a piece
preserves orbit sums.  For the converse, induct on `|F|`.  Fix `y_0` with
stabilizer `K`.

* *If `K = F`,* then `f(y_0) = phi_f(y_0) = phi_g(y_0) = g(y_0)`.  Choose an
  `F`-invariant clopen neighbourhood `V` of `y_0` on which `f` and `g` are
  constant.  Then `f = g` on `V`.
* *If `K != F`,* choose a `K`-invariant clopen neighbourhood `U` of `y_0` with
  `tU cap U` empty for `t notin K`.  Then `F U` is the disjoint union of the
  sets `sU` over cosets `sK`, and `F y cap U = K y` for `y in U`.
  * Moving `f 1_(sU)` by `s^(-1)` gives `f 1_(FU) ~_F f_U`, supported in `U`,
    with `phi^K_(f_U) = phi^F_f` on `U`.  The same holds for `g`.
  * By induction `f_U ~_K g_U`, so `f 1_(FU) ~_F g 1_(FU)`.
* By compactness, finitely many such invariant clopen sets cover `Y`.
  Invariant clopen subsets of either kind are again of the same kind, so they
  can be made disjoint.  Then add up.

The same partition shows that an orbit-sum function `phi_h` with
`h in C(Y, Z)` and `phi_h >= 0` pointwise equals `phi_k` for some
`k in C(Y, N)`.

* On regions of the first kind, `h` is constant near the fixed point.
* On regions of the second kind, pass to `h_U` and induct.

Hence `S(Y, F)` is isomorphic to the monoid of pointwise nonnegative orbit-sum
functions.  It is cancellative, and its group
`Phi_F = { phi_h : h in C(Y, Z) }` carries the pointwise order, so it is
unperforated.

Refinement of `S(Y, F)` follows from refinement of `C(Y, N)`, by refining the
pieces of an equidecomposition against both decompositions.  A cancellative
conical refinement monoid is the positive cone of an interpolation group.  So
`Phi_F` is a dimension group.

**Step B: locally finite `H`.**  Write `H` as the union of finite subgroups
`H_1 subset H_2 subset ...`.

* An equidecomposition uses finitely many group elements.  So `f ~_H g` iff
  `f ~_(H_n) g` for some `n`, and `S(X, H)` is the direct limit of the
  monoids `S(X, H_n)`.
* It is cancellative as a direct limit of cancellative monoids.
* `K^0(X, H) = lim Phi_(H_n)`, with positive maps `phi^(n)_f |-> phi^(n+1)_f`,
  is a dimension group.
* It is simple: finitely many `H`-translates of a nonempty clopen set cover
  `X`.
* It is noncyclic.  `H` is amenable, so an invariant probability measure `mu`
  exists.  It has full support by minimality and no atoms, since orbits are
  infinite.  So there are nonempty clopen sets of arbitrarily small measure,
  and the induced state takes arbitrarily small positive values on nonzero
  positive classes, which a cyclic simple dimension group does not allow.

So (SM) holds, and parts 1--3 apply.
