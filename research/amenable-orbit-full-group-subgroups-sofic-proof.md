---
rg: 2
id: amenable-orbit-full-group-subgroups-sofic-proof
kind: route
title: Orbit patches over Følner sets, sampled from the invariant measure, give sofic approximations
target: amenable-orbit-full-group-subgroups-are-sofic
requires: []
---

Notation as in the claim. Replace `X` by the invariant Borel set `X_free` of
measure one; every `g` in `W(Lambda ~ X)` preserves it, since `g(x)` lies in the
orbit of `x`. Write `g` for `rho(g)`.

**Step 0: the cocycle identity.** For `y` in `X_free` and `g, h` in `Gamma`,

```text
c_(gh)(y) = c_g(h y) c_h(y),        and   g y = y  iff  c_g(y) = 1.     (C)
```

Both hold because `gh(y) = c_g(hy) c_h(y) y` and `lambda y = kappa y` forces
`lambda = kappa` at a free point.

**Step 1: the model.** Fix a finite `F ⊆ Gamma` containing `1` and closed under
the products needed below (it suffices to take all pairs `g, h` with `g, h, gh`
in `F`). Let `E ⊆ Lambda` be the union of the finite ranges of `c_g` for `g` in
`F`. Take a finite nonempty `Q ⊆ Lambda`, points `x_1, ..., x_M` in `X_free`,
and put `Omega = Q × [M]`. For `g` in `F` define a partial map on `Omega`:

```text
sigma_g(lambda, j) = (c_g(lambda x_j) lambda, j)   whenever c_g(lambda x_j) lambda ∈ Q.
```

It is injective on its domain: if `c_g(lambda x_j) lambda = c_g(lambda' x_j) lambda' = kappa`,
then `g(lambda x_j) = kappa x_j = g(lambda' x_j)`, so `lambda x_j = lambda' x_j`
and `lambda = lambda'` because `x_j` is free. Extend it to a permutation of
`Q × {j}` for each `j`, arbitrarily. For `g = 1`, `c_1 = 1` and `sigma_1 = id`.

**Step 2: the defect is controlled by the Følner ratio.** Put

```text
beta(Q) = |{lambda ∈ Q : E lambda ⊄ Q}| / |Q|  <=  sum_(e ∈ E) |eQ \ Q| / |Q|.
```

(The set `{lambda ∈ Q : e lambda ∉ Q}` has the cardinality of `eQ \ Q`.)
Let `g, h, gh` lie in `F`, and let `lambda` be in `Q` with `E lambda ⊆ Q`. Put
`y = lambda x_j`. Then `kappa = c_h(y) lambda` lies in `Q`, so
`sigma_h(lambda, j) = (kappa, j)`. At `kappa x_j = h y`, identity (C) gives
`c_g(h y) kappa = c_(gh)(y) lambda`, which lies in `E lambda ⊆ Q`. So both
`sigma_g(kappa, j)` and `sigma_(gh)(lambda, j)` equal `(c_(gh)(y) lambda, j)`. Hence

```text
d_H(sigma_g sigma_h, sigma_(gh)) <= beta(Q),
```

deterministically, whatever the points `x_j`.

**Step 3: fixed points are sampled from the measure.** On the domain of
`sigma_g`, (C) says `(lambda, j)` is fixed iff `lambda x_j ∈ Fix(g)`. Outside
the domain, which has proportion at most `beta(Q)`, the extension may add fixed
points. So

```text
|Fix sigma_g| / |Omega| <= (1/M) sum_j Z_j(g) + beta(Q),
Z_j(g) = (1/|Q|) sum_(lambda ∈ Q) 1_(Fix g)(lambda x_j)  ∈ [0, 1].
```

Choose `x_1, ..., x_M` independently from `mu`. Invariance of `mu` gives
`mu(lambda^-1 Fix g) = mu(Fix g)`, so each `Z_j(g)` has mean `mu(Fix g)`, and the
`Z_j(g)` are independent in `j` for fixed `g`. By Chebyshev,

```text
P( |(1/M) sum_j Z_j(g) - mu(Fix g)| > t ) <= 1 / (4 M t^2).
```

For `M > |F| / (4 t^2)` a union bound over `g` in `F` leaves positive
probability, so some choice of points gives, for all `g` in `F`,

```text
d_H(sigma_g, id) >= 1 - mu(Fix g) - t - beta(Q).                        (D)
```

**Step 4: amplification.** Let `delta = min_(g ∈ F \ {1}) (1 - mu(Fix g)) / 2`,
which is positive by hypothesis. Given `epsilon > 0`, choose `m` with
`(1 - delta)^m < epsilon`, then `t = delta / 2`, then a Følner set `Q` with
`beta(Q) < min(delta / 2, epsilon / m)` (it exists because `Lambda` is amenable
and `E` is finite), then `M` and the points as in Step 3. Let `sigma^(m)_g` act
coordinatewise on `Omega^m`. A union bound over coordinates gives

```text
d_H(sigma^(m)_g sigma^(m)_h, sigma^(m)_(gh)) <= m beta(Q) < epsilon,
```

and fixed-point proportions multiply, so for `g != 1` in `F`, by (D),

```text
d_H(sigma^(m)_g, id) = 1 - (|Fix sigma_g| / |Omega|)^m >= 1 - (1 - delta)^m > 1 - epsilon.
```

Since `F` and `epsilon` were arbitrary, `Gamma` is sofic. Without amplification,
Steps 2 and 3 with `t -> 0` and `beta(Q) -> 0` show that fixed-point proportions
of the unamplified models are at most `mu(Fix g) + o(1)`; applying the same
count to fixed points on the domain from below gives
`mu(Fix g) - o(1)`, so the models realize the trace `g -> mu(Fix g)`. ∎

**Corollary.** Under the topological hypotheses, a continuous `c_g` on compact `X`
has finite range, and `g != 1` moves a nonempty open set `U`. Full support gives
`mu(U) > 0`, so `mu(Fix g) < 1`. Apply the theorem to the inclusion. ∎

**Hypothesis checks.**
- *Essential freeness is used* in Step 1 (injectivity) and in (C). Without it,
  the partial maps can collide.
- *Finite range is used* to make `E` finite. Countable range would need a
  truncation to a set of large measure, which is not needed for topological
  full groups.
- *A trivial model fails the hypothesis:* the trivial action gives
  `mu(Fix g) = 1`, and the theorem then says nothing.
- *A real object satisfies it:* `Z^2` acting on a free minimal subshift with its
  invariant measure, and the derived full group of `minimal-z2-subshift-derived-full-groups-are-fg-simple`.
