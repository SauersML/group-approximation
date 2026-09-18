---
rg: 2
id: aff-n-over-z-localized-at-ell-is-rf-and-self-similar-proof
kind: route
title: Direct proof of residual finiteness and the finite-state self-similar affine action of Aff_n(Z_(l))
target: aff-n-over-z-localized-at-ell-is-rf-and-self-similar
requires: []
---

Complete direct proof. `Z_(l) = Q ∩ Z_l`, so `Z_(l) ∩ l^k Z_l = l^k Z_(l)`.

**1. Residually finite.** Reduction modulo `l^k` is a ring homomorphism
`Z_(l) -> Z/l^k`, since denominators prime to `l` are invertible mod `l^k`. It
gives homomorphisms `Aff_n(Z_(l)) -> Aff_n(Z/l^k)` onto finite groups. An element
`x -> gx + b` in all their kernels has the entries of `g - I` and `b` in
`∩_k l^k Z_(l) = 0`. If `l ∉ P` then `Z[1/P] ⊆ Z_(l)`, so
`GL_n(Z[1/P]) <= GL_n(Z_(l)) <= Aff_n(Z_(l))`.

**2. Tree action, faithfulness, self-similarity.**
- *Tree action.* `g(x + l^k y) + b = (gx + b) + l^k(gy)` with `gy in Z_l^n`, so
  cosets of `l^k Z_l^n` go to cosets of `l^k Z_l^n`, compatibly with inclusions.
- *Faithful.* If `gx + b = x` for all `x`, then `x = 0` gives `b = 0`, and then
  `g = I`.
- *Self-similar.* Code `x = a + l y` with `a in D = {0, ..., l-1}^n`. Let
  `a' in D` satisfy `ga + b ≡ a' (mod l)`. Then
  `c = (ga + b - a')/l in Z_(l)^n ∩ Z_l^n = Z_(l)^n`, and
  `g(a + l y) + b = a' + l(gy + c)`. So the first-level permutation is
  `a -> a'`, and the section at `a` is `y -> gy + c`.

**3. Finite-state.** Fix `f = (x -> gx + b)`. Let `d >= 1` be prime to `l` with
`d g` and `d b` integral, and let `‖·‖` be the max-norm. Define
`T(a, c) = (ga + c - a')/l` as in 2.
- *The denominator stays `d`.* If `c in (1/d) Z^n` then `d(ga + c - a')` is
  integral and divisible by `l` in `Z_(l)`, so `T(a, c) in (1/d) Z^n`.
- *The size stays bounded.* Put `M = n ‖g‖ (l - 1) + (l - 1)`. Then
  `‖T(a,c)‖ <= (M + ‖c‖)/l`. So with `R = max(‖b‖, M/(l-1))`, `‖c‖ <= R` implies
  `‖T(a,c)‖ <= R`.
- Every section of `f` at any vertex is `y -> gy + c` with `c` obtained from `b`
  by iterating `T`. So `c` lies in the finite set `(1/d)Z^n ∩ [-R, R]^n`.

**4. Finitely generated subgroups.** The entries of finitely many generators and
their inverses have a common denominator `m`, prime to `l`. So they generate a
subgroup of `Aff_n(Z[1/m])`. ∎
