---
rg: 2
id: fp-torsion-presentations-have-positive-orbifold-char-proof
kind: route
title: Reidemeister–Schreier in a finite-index normal subgroup keeps one conjugate per u_r-orbit, and torsion forces nonpositive deficiency
target: fp-torsion-presentations-have-positive-orbifold-char
requires: []
---

Let `q: G -> Q` be onto with kernel `H`, and put `N = |Q| = [G:H]`. Let
`pi: F = F(X) -> G` be the quotient map and `E = pi^(-1)(H)`, a normal
subgroup of index `N` in `F`. By Schreier's formula, `E` is free of rank
`1 + N(|X| - 1)`. Let `M` be the normal closure of `R` in `F`. Then
`M <= E` and `H = E/M`.

**Step 1: generating `M` inside `E`.** Let `T` be a transversal of `E` in
`F`. Every `f in F` is `f = e t` with `e in E` and `t in T`, and
`f r f^(-1) = e (t r t^(-1)) e^(-1)`. So `M` is the normal closure in `E` of
`{ t r t^(-1) : t in T, r in R }`.

**Step 2: one conjugate per orbit.** Fix `r = u^n` with `u = u_r`, and let
`m = o_Q(r)`, the least `m >= 1` with `u^m in E`. Right multiplication by `u`
permutes the `N` cosets `E t`. Because `E` is normal, `E t u^j = E t` if and
only if `u^j in E`, so every orbit has exactly `m` cosets. If `E t' = E t u`,
write `t' = e t u` with `e in E`. Since `u r u^(-1) = u^(n+1) u^(-1) = r`,

```text
t' r t'^(-1) = e t (u r u^(-1)) t^(-1) e^(-1) = e (t r t^(-1)) e^(-1).
```

So transversal conjugates of `r` in one orbit are conjugate in `E`, and one
per orbit gives the same normal closure. Hence `H` has a presentation with
`1 + N(|X| - 1)` generators and `sum_r N/o_Q(r)` relators. Its deficiency is

```text
d_H = 1 + N (|X| - 1 - sum_r 1/o_Q(r)) = 1 - N chi_Q(X,R).
```

**Step 3: torsion forces `d_H <= 0`.** A presentation with `g` generators and
`s` relators gives `H_1(-; Q)` as the cokernel of an `s x g` rational matrix,
so its rank is at least `g - s`. `H` is finitely generated, being of finite
index in `G`, and it is torsion, being a subgroup of `G`. So `H_1(H; Z)` is a
finitely generated torsion abelian group, hence finite, and
`H_1(H; Q) = 0`. Therefore `d_H <= 0`, which means `chi_Q(X,R) >= 1/N`.

**Step 4: residually finite case.** Each `u_r` has finite order `o_G(r)` in
`G`. For every proper divisor `d` of `o_G(r)` we have `u_r^d != 1`, and
residual finiteness gives a finite quotient in which `u_r^d != 1`. There are
finitely many such pairs `(r, d)`. Intersecting the kernels gives a finite
quotient `Q` with `o_Q(r) = o_G(r)` for all `r`. Step 3 then gives
`chi_G(X,R) = chi_Q(X,R) >= 1/|Q| > 0`. ∎

**Check on `A_5 = <a, b | a^2, b^3, (ab)^5>`, `Q = A_5`, `H = 1`.** Step 2
gives a presentation of the trivial group with `1 + 60 = 61` generators and
`30 + 20 + 12 = 62` relators, deficiency `-1 = 1 - 60 * (1/30)`.
