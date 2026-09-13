---
rg: 2
id: irs-rigid-kazhdan-haagerup-orbit-full-groups-proof
kind: route
title: Induce a proper affine action along the translation cocycle, fix a point by (T), and count translations on free points
target: irs-rigid-kazhdan-groups-avoid-haagerup-orbit-full-groups
requires: []
---

Write `g` for `rho(g)`. Discard a null set so that `H` acts freely on `X`.

**Step 0: the cocycle.** For `g in S` and `x in X` let `c(g,x) in H` be the unique element
with `g x = c(g,x) x`; uniqueness is freeness of `H`. Then `c(gh,x) = c(g, hx) c(h,x)`, and
each `c(g, .)` equals `c_(rho(g))` almost everywhere, which has finite range by the definition
of `W(H ~ X)`.

**Step 1: freeness off the fixed set.** Let `F_0 = {x : g x = x for all g in S}` and
`Y = X \ F_0`. Both are Borel and `S`-invariant. Suppose `mu(Y) > 0`. The stabilizer law of
`S ~ (Y, mu/mu(Y))` is an invariant random subgroup, hence `p delta_S + (1-p) delta_e`. No
point of `Y` has stabilizer `S`, so `p = 0`, and almost every `x in Y` has trivial
stabilizer.

**Step 2: a proper affine action of `H`.** By the Haagerup property there are a real Hilbert
space `K`, an orthogonal representation `pi` of `H` on `K` and a cocycle `b : H -> K`,
`b(hk) = b(h) + pi(h) b(k)`, with `||b(h)|| -> infinity` as `h -> infinity`.

**Step 3: the induced affine action.** On `L^2(Y, K)` put

```text
(g . f)(x) = pi(c(g, g^(-1)x)) f(g^(-1)x) + b(c(g, g^(-1)x)).          (HF1)
```

- The translation part is bounded, since `c(g, .)` has finite range, so `g . f` lies in `L^2`.
- The linear part is an isometry, since `pi` is orthogonal and `g` preserves `mu`.
- The cocycle identities for `c` and `b` give `g . (h . f) = (gh) . f`.

So `(HF1)` is an affine isometric action of `S`.

**Step 4: a fixed point.** A countable group with property (T) has property (FH)
(Delorme--Guichardet; Bekka--de la Harpe--Valette, Theorem 2.12.4). So some `f_0` is fixed:

```text
f_0(g x) = pi(c(g,x)) f_0(x) + b(c(g,x))      for a.e. x in Y, every g.   (HF2)
```

Hence `||b(c(g,x))|| <= ||f_0(g x)|| + ||f_0(x)||`.

**Step 5: bounded translations on half of `Y`.** Choose `R` with
`mu{x in Y : ||f_0(x)|| > R} <= mu(Y)/4`. Each `g` preserves `mu` and `Y`, so the same bound
holds for `x -> ||f_0(g x)||`. Therefore

```text
mu{x in Y : c(g,x) in F} >= mu(Y)/2      for every g in S,              (HF3)
F = {h in H : ||b(h)|| <= 2R},  a finite set by properness.
```

**Step 6: counting.** For almost every `x in Y` the map `g -> c(g,x)` is injective: if
`c(g,x) = c(g',x)` then `g x = g' x`, so `g^(-1) g'` fixes `x` and is trivial by Step 1.
Thus `|{g : c(g,x) in F}| <= |F|`. As `S` is countable, Tonelli gives

```text
sum over g in S of mu{x in Y : c(g,x) in F} = integral over Y of |{g : c(g,x) in F}| <= |F| mu(Y).
```

By `(HF3)` every term of the sum is at least `mu(Y)/2`, and `S` is infinite, so the sum is
infinite. This contradiction shows `mu(Y) = 0`.

**Where rigidity entered.** Only in Step 6, to make `g -> c(g,x)` injective. Without it,
Steps 2--5 still hold, and the count shows that stabilizers are infinite on a subset of `Y` of
positive measure.
