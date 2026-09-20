---
rg: 2
id: fpbs-cs-set-family-hypothesis-fails-commuting-normal-cross-proof
kind: route
title: A conjugate of a short element by a commuting-cross point is a K-commutator times an H-conjugate, so two small factor sets trap a quadratically larger core
target: fpbs-cs-set-family-hypothesis-fails-commuting-normal-cross
requires: []
artifacts:
  - research/artifacts/fpbs-acylindrical-l2-gap-2026-09-16.md
  - experiments/fpbs-commuting-cross-2026-09-17/check_commuting_cross.py
  - experiments/fpbs-commuting-cross-2026-09-17/output.txt
---

This proof is complete and self-contained. It uses only the *statement* of
Choi–Seo `thm:hutchcroft1plus2` (artifact, CS4), and nothing about its truth or
its proof. The notation is that of the target.

## Step 1. The necessary condition

Call `a ∈ A` **good** if some `h ∈ B(R)` has `a h a^-1 ∉ A A^-1`.

We show that SF(𝓗,R) forces at least `#A/2` good points in every finite `A`.
This is part (a) of `fpbs-cs-set-family-hypothesis-fails-infinite-centre`,
reproved here in full.

Take `a ∈ A'`, where `A'` is the set SF provides, and take the `g, h` it gives.
Then `‖h‖_S <= R`, `A ⊆ a H(g)` and `H(g) ∩ h H(g) = ∅`.

Suppose `a h a^-1 = u v^-1` with `u, v ∈ A`. Then `a^-1 u = h a^-1 v`. The left
side lies in `a^-1 A ⊆ H(g)`. The right side lies in `h a^-1 A ⊆ h H(g)`. These
sets are disjoint, a contradiction. So every point of `A'` is good, and
`#A' >= #A/2`.

## Step 2. The key identity

Let `x ∈ H`, `y ∈ K` and `h ∈ G`. Since `K` is normal, the element
`[y,h] = y (h y^-1 h^-1)` is a product of two elements of `K`, so it lies in
`K`. Also `y h y^-1 = [y,h] h`. Since `x` commutes with every element of `K`,

```text
(x y) h (x y)^-1 = x (y h y^-1) x^-1 = x [y,h] h x^-1 = [y,h] (x h x^-1).
```

## Step 3. Every core point is bad

Let `a = x y` with `x ∈ X` and `y ∈ Y`, and let `h ∈ B(R)`. Put

```text
u = [y,h] ∈ C_2,        v = x h^-1 x^-1 ∈ C_1 .
```

Then `v^-1 = x h x^-1`, and Step 2 gives `a h a^-1 = u v^-1`. Both `u` and `v`
lie in `A`, so `a h a^-1 ∈ A A^-1`. This holds for every `h ∈ B(R)`, so `a` is
not good.

## Step 4. Counting

*The core has `n^2` elements.* Suppose `x y = x' y'` with `x, x' ∈ X` and
`y, y' ∈ Y`. Then `x'^-1 x = y' y^-1`, which lies in `H ∩ K`. So `x` and `x'`
lie in the same coset of `H ∩ K`. By the choice of `X` this gives `x = x'`, and
then `y = y'`. Hence `#(X Y) = n^2`.

*The choices are possible.* `H ∩ K` has infinite index in `H` and `K` is
infinite, so `X` and `Y` exist for every `n`.

*The good points are too few.* By Step 3 the good points lie in `A \ X Y`,
which is contained in `C_1 ∪ C_2`. So

```text
#good <= #C_1 + #C_2 <= 2 n #B(R) < n^2 = #(X Y).
```

Since `#A = #(X Y) + #(A \ X Y)` and `#good <= #(A \ X Y)`, we get
`#good < #A / 2`.

By Step 1, SF(𝓗,R) fails. Nothing constrained `𝓗`, `R` or `S`: `R` enters only
through the choice `n > 2 #B(R)`, which is available for every `R`. ∎

## Step 5. The class statements

*Direct products `H x K`* with both factors infinite. Take `K` to be the second
factor, which is normal. Then `H ∩ K = {e}` has infinite index in `H`, and `H`
commutes with `K`.

*Infinite centre `Z` with `[G:Z] = infinity`.* Take `K = Z` and `H = G`.

*Equivalent form.* If `H` and `K` are as in the theorem, then
`H <= C_G(K)`, and `H ∩ K` has infinite index in `H`. So `C_G(K)` has infinite
image in `G/K`. Conversely, take `H = C_G(K)`.

*Overgroups.* The hypotheses mention only `K ⊴ G`, `[H,K] = 1` and the two
indices. So they persist in any group containing `H` and `K` in which `K` stays
normal.

## Step 6. Machine check

`check_commuting_cross.py` builds `A` for five cases, listed with their
`output.txt` line:

* `F_2 x F_2` with product generators, `n = 20` and `n = 40`, `R = 1`,
  `#B(1) = 9`;
* `F_2 x F_2` with a mixed generating set;
* `F_2 x D_infinity` with a mixed generating set;
* `F_2 x Z`.

It decides membership `a h a^-1 ∈ A A^-1` by testing whether
`(a h a^-1) A ∩ A` is nonempty over all of `A`. It asserts that every core
point is bad and that `#good < #A/2`. All assertions pass.
