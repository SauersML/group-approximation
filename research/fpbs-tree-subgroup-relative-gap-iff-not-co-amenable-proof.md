---
rg: 2
id: fpbs-tree-subgroup-relative-gap-iff-not-co-amenable-proof
kind: route
title: Word recursion on the Schreier graph, Pringsheim at both radii, and a Cheeger bound from the absence of an invariant mean
target: fpbs-tree-subgroup-relative-gap-iff-not-co-amenable
requires:
  - fpbs-relative-gap-along-any-subgroup-separates
  - fpbs-non-co-amenable-subgroups-have-schreier-spectral-gap
artifacts:
  - experiments/fpbs-schreier-kesten-2026-09-17/verify_schreier_cogrowth_identity.py
---

Notation is that of the claim. Standard facts used:
- Pringsheim's theorem: a power series with nonnegative coefficients and finite
  radius `R` has no holomorphic extension to any neighbourhood of `R`;
- the identity theorem and the holomorphic inverse function theorem;
- Cauchy–Hadamard.

**1. Two-point function.** `T` is a tree, so `P_p(o <-> h) = p^|h|`, and
`chi^H_p = sum_(h in H) p^|h| = F_H(p)` in `[0, infinity]`.

**2. Word recursion on cosets.** Let `A` be the adjacency operator of `X`,
`A(x,y) = #{s in S : xs = y}`. Let `A_n(x,y)` count the reduced words `w` of
length `n` with `xw = y`, and `A_0 = I`. Appending a letter `s` to a reduced
word `w` of length `n` gives either a reduced word of length `n+1` or, when `s`
cancels the last letter, a reduced word `w'` of length `n-1`. Each `w'` arises
this way from `q` words `w` if `n >= 2`, and from `q+1` if `n = 1`. Hence

```text
A_1 A = A_2 + (q+1) I,        A_n A = A_(n+1) + q A_(n-1)   (n >= 2).
```

This is a statement about words acting on cosets, and it uses no normality.
For `B(s) = sum_n A_n s^n` this gives `B(s) ((1 + q s^2) I - s A) = (1 - s^2) I`
as formal power series with matrix coefficients. The graph `X` is locally
finite, so every coefficient of every product is a finite sum, and the product
is associative. The inverse of `(1 + q s^2) I - s A` is
`sum_m s^m A^m (1 + q s^2)^(-(m+1))`. Taking the `(H,H)` entry, and using
`A_n(H,H) = f_n(H)` and `A^m(H,H) = W_m`:

```text
F_H(s) = (1 - s^2) sum_m W_m s^m (1 + q s^2)^(-(m+1)) = phi(s) sum_m W_m z(s)^m .
```

`W_m <= (q+1)^m`, so the double series converges absolutely when
`(q+1)|s| / (1 - q|s|^2) < 1`. There the rearrangement is valid, and this is
item 1. The script in `artifacts` checks the coefficient identity for
`n <= 9` on three non-normal subgroups of `F_2`.

**3. The radius of `Gamma(zeta) = sum_m W_m zeta^m`.** By Cauchy–Hadamard it is
`zeta_H = 1/((q+1) rho_H) >= 1/(q+1)`. The map `z` is strictly increasing on
`[0, 1/sqrt q]`, with `z(1/q) = 1/(q+1)` and `z'(1/q) > 0`.

**4. `rho_H < 1` implies `R_H > 1/q`.** Suppose `R_H <= 1/q`. Then
`z([0,R_H]) ⊂ [0, 1/(q+1)]`, which lies strictly inside the disc of radius
`zeta_H`. So `phi · (Gamma ∘ z)` is holomorphic on a thin convex neighbourhood
`V` of `[0, R_H]` (note `1 + q s^2 ≠ 0` near the real segment). `V ∩ {|s| < R_H}`
is convex and contains a neighbourhood of `0`, where the two functions agree by
step 2. The identity theorem glues them into a holomorphic extension of `F_H`
to a neighbourhood of `R_H`, which contradicts Pringsheim. So `R_H > 1/q`.

For `p < R_H` we have `chi^H_p < infinity`. The implication (2 ⇒ 1) in the
proof of `fpbs-relative-gap-along-any-subgroup-separates` then gives no
`H`-infinite cluster at `p`, so `p_c(H;T) >= R_H > 1/q = p_c(T)`. That argument
uses only the invariance of `H` under left multiplication by its own elements,
not normality.

**5. `rho_H = 1` implies `R_H <= 1/q`.** Now `zeta_H = 1/(q+1) = z(1/q)`. Suppose
`R_H > 1/q`.
- *The identity holds on `[0, 1/q)`.* For `s < 1/q`, `z(s) < zeta_H`, and the
  argument of step 4 on a thin convex neighbourhood of `[0, 1/q - eps]`, now
  inside the disc of radius `R_H`, gives `F_H = phi · (Gamma ∘ z)` on
  `[0, 1/q)`.
- *A continuation of `Gamma`.* Let `w` be the holomorphic local inverse of `z`
  on a small disc `U` around `zeta_H`, with `w(U)` inside a small disc around
  `1/q` contained in `{|s| < R_H}`. Since `phi(1/q) ≠ 0`, the function
  `G(zeta) = F_H(w(zeta)) / phi(w(zeta))` is holomorphic on `U`, possibly after
  shrinking `U`.
- *The contradiction.* For real `zeta in U` with `zeta < zeta_H`, `w(zeta)` is
  real and below `1/q`, so `G(zeta) = Gamma(zeta)`. The set
  `U ∩ {|zeta| < zeta_H}` is convex, so `G = Gamma` there, and `Gamma` extends
  holomorphically to a neighbourhood of its radius `zeta_H`. This contradicts
  Pringsheim.

So `R_H = 1/q`, and `chi^H_p = F_H(p) = infinity` for every `p > 1/q`, since a
series with nonnegative coefficients diverges beyond its radius.
- *No gap.* Condition 2 of `fpbs-relative-gap-along-any-subgroup-separates`
  fails at every `p > p_c(T)`, so condition 1 fails, and `p_c(H;T) <= p_c(T)`.
- *Equality.* Every `H`-infinite cluster is infinite, so
  `p_c(H;T) >= p_c(T)`, and `p_c(H;T) = 1/q`.

This is item 2.

**6. Item 3.** `F_d` is nonamenable. If `H` is not co-amenable, then part (a)
of `fpbs-non-co-amenable-subgroups-have-schreier-spectral-gap` gives
`rho(Sch(H\F_d,S)) < 1`, and step 4 gives the gap. ∎
