---
rg: 2
id: sparse-fully-branched-covers-iff-sofic-proof
kind: route
title: Run the induced model with the trivial pi_1(X)-model, and get the mark by descending developing maps of K-fixed points to genuine covers
target: sparse-fully-branched-covers-iff-sofic-simple-residual
requires:
  - sparse-branched-covers-with-sofic-pi1-give-sofic-lattice
  - infinite-simple-group-permutation-stable-iff-nonsofic
  - branched-cover-monodromy-reduction-without-connected-links
---

**Step B below is not currently available.**  Refereeing (swarm-0917) found
that it imports Step 4 of `sparse-branched-covers-sofic-pi1-reduction-proof`
together with an unstated hypothesis: every vertex link of `Y` must be
connected.  That hypothesis is now the third prerequisite above,
`branched-cover-monodromy-reduction-without-connected-links`, which is OPEN
and expected to be false in the stated generality.  Step A (3 => 1) is
unaffected and was checked by three referees.  See the `## Attempts` section
of `sparse-fully-branched-covers-iff-sofic-simple-residual` for the
counterexample and the proposed repair.


Notation and Lemmas 1--4 and `(BR)` are those of
`sparse-branched-covers-sofic-pi1-reduction-proof`, the proof of
`sparse-branched-covers-with-sofic-pi1-give-sofic-lattice`.  In addition:
* `kappa: X~ -> X` is the universal covering of a component, so
  `q = p o kappa`, and the fibres of `kappa` on `V = q^(-1)(v)` are the
  `Lambda`-orbits.
* `|g| = d(o, g o)`.
* `rho(x) = d(x, B~)`.

Finite index permanence and passage to subgroups make soficity of `K` and
of `G` equivalent.  For disconnected `X`, apply the constructions to each
component and take disjoint unions.  All the lemmas are local.

## Step A. The trivial model (3 => 1)

**The almost homomorphism.**  Let `X_n`, with sheet number `N_n`, be as in
item 3, and put `T_n = p^(-1)(v)`.  Choose `D_n -> infinity` slowly enough
that
`(c_Y v_Delta(D_n) + 1) beta(X_n) / (1 - beta(X_n)) -> 0`.
Call `t in T_n` *good* if `rho(t) >= D_n`.  By `(BR)`, the good fraction
tends to 1.

For `g in G` and `t in T_n` with `rho(t) > 2|g|`, choose a lift `t~ in V`
and set

```text
Sigma_n(g)(t) = kappa(g * t~).
```

This does not depend on the lift, by Lemma 4.3.  It is injective: by
Lemma 4.1 with `h = g^(-1)`, `g^(-1) * (g * x) = x` whenever
`rho(x) > 2|g|`.  Extend it to a permutation of `T_n` arbitrarily.

For fixed `g, h`, once `D_n > 3(|g| + |h| + |hg|)`, Lemma 4.1 gives
`Sigma_n(h) Sigma_n(g) t = Sigma_n(hg) t` at every good `t`.  So
`(Sigma_n)` is an almost homomorphism `G -> Sym(T_n)`, and so is its
restriction to `K`.  This is Step 3 of the reduction with `M` a point.
Freeness is not claimed.

**The descent lemma.**  `K` acts cocompactly on `Delta`, since it has finite
index in `G`.  Fix `r_0 > 0` such that the `K`-translates of the open ball
`B(o, r_0)` cover `Delta`.  Let

```text
F_K = {k in K : |k| < 2 r_0},
```

a finite set.

**Lemma 5.**  Let `x in V` with `rho = rho(x) > 5 r_0`.  Suppose
`kappa(k * x) = kappa(x)` for every `k in F_K`.  Then the component of
`kappa(x)` in `X` is unbranched.

*Proof.*  Put `dev = dev_(x,o)` and `psi = kappa o dev^(-1): B(o, rho) -> X`.
Then `psi` is a local homeomorphism and local isometry into `X \ B`, with
`p o psi = pi`.

*Invariance.*  Let `k in F_K`.  By hypothesis `k * x = lambda x` for some
`lambda in Lambda`, and `d(x, lambda x) = |k|`.
* By Lemmas 2.3 and 2.2,
  `dev_(lambda x, o) = k o dev_(lambda x, k^(-1) o) = k o dev` on
  `B(lambda x, rho - |k|)`.
* By Lemma 2.1, `dev_(lambda x, o) = dev o lambda^(-1)` there.

So `dev(lambda^(-1) a) = k dev(a)` for `a in B(x, rho - 2|k|)`, a set
contained in `B(lambda x, rho - |k|)`.  Applying `kappa`:

```text
psi(k z) = psi(z)     for all z in B(o, rho - 2|k|).                 (INV)
```

*Descent.*  For `z in Delta`, pick `k in K` with `k z in B(o, r_0)` and set
`s(z) = psi(k z)`.  Suppose `k'` also works, and put `h = k' k^(-1)` and
`w = k z`.  Then

```text
|h| <= d(o, h w) + d(h w, h o) < 2 r_0,
```

so `h in F_K`.  Also `w in B(o, r_0)`, which lies inside
`B(o, rho - 2|h|)` because `rho > 5 r_0`.  So (INV) gives
`psi(h w) = psi(w)`, and `s` is well defined.

Near `z` the same `k` works, since the ball is open.  So `s` is locally
`psi o k`: a K-invariant local homeomorphism `Delta -> X \ B`.  Its image
`s(Delta)` has three properties.
* It is open.
* It is compact, being the image of the compact space `Delta / K`.
* It is connected, and it contains `s(o) = psi(o) = kappa(x)`.

So `s(Delta)` is the component of `kappa(x)`, and it misses `B`.  QED

**The mark.**  Assume every `X_n` has branched components carrying a
fraction at least `c` of the sheets.  The fibre `T_n cap C` of a component
`C` with `N_C` sheets has between `N_C - sum_(b in B cap C) d_b` and `N_C`
points, and `sum_b d_b = beta N_n = o(|T_n|)`.  So at least a fraction
`c - o(1)` of `T_n` is good and lies in a branched component.  Once
`D_n > 5 r_0`, `Sigma_n(k)` for `k in F_K` is given by the formula at every
good point, because `2|k| < 4 r_0`.

By Lemma 5, each such `t` is moved by `Sigma_n(k)` for some
`k in F_K \ {1}`.  Summing over `F_K`, some `k_n in F_K \ {1}` has
`d_H(Sigma_n(k_n), 1) >= (c - o(1)) / |F_K|`.  `F_K` is finite, so a
single `k` occurs for infinitely many `n`.  Pass to that subsequence.

Then `Sigma_n|_K` is an almost homomorphism of the infinite simple group
`K` with `d_H(Sigma_n(k), 1) >= c / (2|F_K|)` for large `n`.  By
`infinite-simple-group-permutation-stable-iff-nonsofic` ((1) => (2)),
`K` is sofic.

## Step B. Sparse fully branched covers from soficity (1 => 2)

`G` is sofic.  Fix `g in K \ {1}` and a word `u` of length `l` in the
`f_i^(+-1)` whose image in `G` is `g`.  The `k_i` generate `G`, since
`pi_1(Y°) -> G` is onto.

Run Step 4 of the reduction proof with an `(F', epsilon)`-sofic model
`Sigma` on `[n]`, with `F'` also containing the images of all prefixes of
`u`.  This produces `X_n`, whose components are the orbits `O` of
`<Sigma(k_i)>` on `[n]`, and

```text
beta(X_n) n <= (#words)(L+1) epsilon n.
```

*Unbranched orbits are fixed by u.*  Let `O` be the orbit of an unbranched
component.
* Every cone point of that component has degree 1, so every
  `Sigma(w_(y,j))` fixes `O` pointwise.
* `O` is invariant, so every conjugate of these words also acts trivially
  on `O`.
* So the action of the free group on `O` factors through `G`.
* `K` is infinite simple and `O` is finite, so `K` acts trivially on `O`.

Hence `Sigma(u) = Sigma(k_(i_1))^(+-1) ... Sigma(k_(i_l))^(+-1)` fixes `O`
pointwise.

*Few points in unbranched orbits.*  Chaining multiplicativity along the
prefixes of `u`, `Sigma(u)` differs from `Sigma(g)` on at most
`(l + 1) epsilon n` points.  Freeness gives `Sigma(g)` at most
`epsilon n` fixed points.  So `Sigma(u)` fixes at most
`(l + 2) epsilon n` points, and at most that many points lie in unbranched
orbits.

*Remove them.*  Deleting the unbranched components leaves a fully
branched cover `X'_n` with at least `(1 - (l+2) epsilon) n` sheets and the
same branch set.  Therefore

```text
beta(X'_n) <= (#words)(L+1) epsilon / (1 - (l+2) epsilon) -> 0 .
```

## Step C. 2 => 3

This is immediate, with `c = 1`.

## Step D. The Titz--Witzel consequences

Suppose the component `C` is unbranched.  Then `p|_C` is a proper local
homeomorphism onto the connected space `Y`, hence a finite covering.  So
`C~ = Delta` and `C = Delta / Gamma'` with `Gamma' <= G` of finite index.

Its degree is `[G : Gamma'] <= [G : G^(infinity)]`, since `Gamma'`
contains the finite residual.

For `Y_1^2`, `Delta` is a `C~_2` building.  An apartment is an isometrically
embedded Euclidean plane.  Its closed `R`-disk maps locally isometrically
into `C`, which lies in `X \ B`.  So condition (H) fails for every `R`.
Hence the covers of `titz-witzel-flat-hitting-sparse-branched-covers` are
fully branched, and Step A applies to them.  QED
