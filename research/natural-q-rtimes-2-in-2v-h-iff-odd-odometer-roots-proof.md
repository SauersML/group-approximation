---
rg: 2
id: natural-q-rtimes-2-in-2v-h-iff-odd-odometer-roots-proof
kind: route
title: A natural odd translation in 2V_H agrees on a rectangle with a basic bisection whose coefficient is a translation of the same odd denominator; sections give the odometer, Bézout gives all of Z_(2), and the converse is the affine construction
target: natural-q-rtimes-2-in-2v-h-iff-odd-odometer-roots
requires:
  - affine-2v-hosts-reach-z-1-2n-by-doubling-but-not-q
---

Lane proof (bh-free-16, 2026-09-18). Notation as in the claim. `A(H) = {c ∈ Z_2 : T_c ∈ H}`, a subgroup of `Z_2`.

## Step 1. Roots of the odometer

- **Centralizer.** If `g ∈ Aut(T_2)` commutes with `T_1`, then `g(n) = g(T_1^n 0) = T_1^n g(0) = n + g(0)` for
  `n ∈ Z`. `Z` is dense in `Z_2`, so `g = T_(g(0))`. Hence `C(T_1) = {T_c : c ∈ Z_2}`.
- **Roots.** An `m`-th root of `T_1` commutes with `T_1`, so it is some `T_c` with `mc = 1`. This forces `m` odd and
  `c = 1/m`.
- So "`T_1` and all its odd roots lie in `H`" is equivalent to `Z_(2) = ∪_(m odd) (1/m)Z ⊆ A(H)`.

## Step 2. Sections of translations

For `c ∈ Z_2` and a digit `i`: `T_c(i + 2y) = j + 2(y + c')`, with `j ≡ c + i (mod 2)` and `c' = (c + i − j)/2`. So
`T_c|_i = T_(c')`, and `A(H)` is closed under these sections because `H` is self-similar.
- **Even `c`.** The section at `0` is `T_(c/2)`.
- **Odd `c`.** The sections at `0` and `1` are `T_((c−1)/2)` and `T_((c+1)/2)`, which differ by `T_1`.
- **So `A(H) ≠ 0` implies `1 ∈ A(H)`.** Take `c ≠ 0` in `A(H)` and pass along `0^v`, where `v = v_2(c)`, to the odd
  element `c/2^v`. Then take the two sections.
- **Denominators are preserved.** If `c = k/m` with `m` odd, then `c' = ((k + (i − j)m)/2)/m`, and its numerator is
  `≡ 2^-1 k (mod m)`. So sections keep the exact denominator `m`, and `c' ≠ 0` whenever `m > 1`.

## Step 3. Necessity

Suppose the natural translation by `1/q` (`q` an odd prime) lies in `2V_H`.
- **It is a colour-1 map.** `1/q ∈ Z_2` has no negative-position digits, and carries go upward, so it acts as
  `T_(1/q) × id`.
- **It agrees with a basic bisection.** By the normal form of `2V_H` (affine node, Step 2B), it agrees on some
  rectangle `C(p) × C(w)` with `(p x', w y') ↦ (p' h(x'), w' y')`, where `h ∈ H`. This uses that `H` fixes colour-2
  edges with restriction itself.
- **The colour-2 side.** Colour 2 is unchanged, so `w' = w`.
- **The colour-1 side.** Let `b, b'` be the integer values of `p, p'`. For all `x'`,
  `b + 2^j x' + 1/q = b' + 2^(j') h(x')`.
  - `h` is a tree automorphism, so it preserves 2-adic distances. This forces `j = j'`.
  - Then `h = T_c` with `c = (b − b' + 1/q)/2^j`.
  - `2^j c = b − b' + 1/q` has denominator exactly `q`, so `c ∈ A(H)` has denominator `q`.

This gives item 2's hypothesis for every odd prime `q`. With Step 2, `1 ∈ A(H)`. For `c = k/q` with `gcd(k, q) = 1`,
write `αk + βq = 1`. Then `1/q = αc + β ∈ A(H)`. So `(1/q)Z ⊆ A(H)` for every odd prime `q`, hence
`Z_(2) ⊆ A(H)`, since `A(H)` is a group.

## Step 4. Sufficiency

Assume `Z_(2) ⊆ A(H)`.
- **Odd part.** For `c ∈ Z_(2)`, `T_c × id` is a global bisection of the groupoid, so it lies in `2V_H`. It is the
  natural translation by `c`.
- **Dyadic part and the dilation.** `u ∈ 2V` is the natural multiplication by `2`, so `u^-k (T_c × id) u^k` is the
  natural translation by `c/2^k`.
- **All of `Q`.** Every rational is `c/2^k` with `c ∈ Z_(2)`, so all natural translations by `Q` and the dilation `u`
  lie in `2V_H`.
- **Faithfulness.** The natural action is faithful, and `2V_H` acts faithfully on `X` (affine node, Step 2B, under
  the stated groupoid conditions). So this is a copy of `Q ⋊ ⟨2⟩`.

## Step 5. Necessary shape of H

- **Not contracting.** Take a finite nucleus `N` and `m > 1` odd. Deep sections of `T_(1/m)` lie in `N`, and by Step 2
  they are translations of exact denominator `m`. As `m` varies these are infinitely many distinct elements, which
  is a contradiction.
- **Not polynomial activity.** By Step 2 every section of `T_(1/m)` is a translation with denominator `m > 1`, so it
  is nontrivial. So level `n` has `2^n` nontrivial sections.
- **Not finitely generated affine.** This is the Limit step of the affine node: coefficients lie in some `Z[1/N']`,
  so `1/q ∉ A(H)` for primes `q ∤ 2N'`.

## Step 6. Host side

Steps A–D of `affine-2v-hosts-reach-z-1-2n-by-doubling-but-not-q-proof` are stated for `G_N`. They go through for any
self-similar `H` that is pseudo-free and whose fixed sets have empty interior with Hausdorff germ groupoid. These are
exactly the properties Steps A–B verify there for affine maps.
- Li, Example ex:ZS (III), with `D^*(w,w) = H` then gives type `F_n` from type `F_n` of `H`.
- Matui's Theorem simple2 gives simplicity, since perfectness is Step D verbatim.

Item 4 of the claim is conditional on exactly these hypotheses. ∎
