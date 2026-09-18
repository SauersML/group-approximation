---
rg: 2
id: odometer-generators-carry-no-nonsolvable-baumslag-solitar-proof
kind: route
title: The centralizer of a minimal odometer power consists of fibrewise translations, which commute with the odometer; Britton's lemma makes the forced commutator nontrivial
target: odometer-generators-carry-no-nonsolvable-baumslag-solitar
requires: []
---

**Standard inputs (not re-read):** Britton's lemma for HNN extensions (Lyndon-Schupp IV.2); a continuous function on a
compact space that is invariant under a minimal homeomorphism is constant.

Conjugating, assume `X = K x Y` and `a = (+1) x id`.

**Step 1 (centralizer of a minimal power).** Suppose `nK = K`, so `a^n = (+n) x id` is minimal on each fibre
`K x {y}`, and these fibres are exactly the orbit closures of `a^n`. Let `F` be a homeomorphism commuting with `a^n`.
- `F` maps orbit closures to orbit closures, so `F(K x {y}) = K x {h(y)}` for a bijection `h` of `Y`, which is a
  homeomorphism because `F` is.
- Write `F(x, y) = (f_y(x), h(y))`. Commuting with `a^n` gives `f_y(x + n) = f_y(x) + n`.
- So `g_y(x) = f_y(x) - x` is continuous and invariant under the minimal map `+n`, hence constant, `g_y = delta(y)`.
- Therefore `F(x, y) = (x + delta(y), h(y))`, and such an `F` commutes with `a = (+1) x id`.

**Step 2 (item 1).** `s = t a t^-1` commutes with `s^m = t a^m t^-1 = a^n`. By Step 1, `s` commutes with `a`.

**Step 3 (item 2).** From `t a^m t^-1 = a^n` we get `t^-1 a^n t = a^m`. If `mK = K`, apply Steps 1 and 2 to the pair
`(a, t^-1)` with the roles of `m` and `n` exchanged: `t^-1 a t` commutes with `a`.

**Step 4 (item 3).** In `BS(m,n) = <a, t | t a^m t^-1 = a^n>`, Britton's lemma says that a word containing `t^{+-1}`
represents `1` only if it contains a pinch `t a^{km} t^-1` or `t^-1 a^{kn} t`. The word
`[t a t^-1, a] = t a t^-1 . a . t a^-1 t^-1 . a^-1` has `t`-segments `t a t^-1` and `t^-1 a t`; these are pinches
only if `m | 1` or `n | 1`. So for `|m|, |n| >= 2` the commutator is nontrivial, and likewise `[t^-1 a t, a]`. By
Steps 2 and 3, one of them maps to `1` in `<a, t>`, so the natural map from `BS(m,n)` is not injective.

**Step 5 (item 4).** Suppose `nK = K`. By induction, `t^k a^{m^k} t^-k = a^{n^k}` for `k >= 1`:
`t^{k+1} a^{m^{k+1}} t^{-(k+1)} = t (t^k a^{m^k} t^-k)^m t^-1 = t a^{m n^k} t^-1 = (t a^m t^-1)^{n^k} = a^{n^{k+1}}`.
- Since `n^k K = K`, Steps 1-2 apply to the pair `(a, t^k)` with exponents `(m^k, n^k)`. So `t^k a t^-k` commutes with
  `a` for every `k >= 1`.
- Conjugating by `t^l`, the elements `x_k = t^k a t^-k` commute pairwise for all `k, l ∈ Z`.
- `N = <x_k : k ∈ Z>` is abelian. It is normal in `<a, t>`: `a = x_0` commutes with every `x_k`, and `t x_k t^-1 = x_{k+1}`.
- `<a, t> = N <t>`, so `<a, t>/N` is cyclic.
- If instead `mK = K`, apply the same argument to `t^-1`, using `t^-1 a^n t = a^m`.

**Remark (explicit case, sketch; not claimed in items 1-4).** Take `K = Z_2`, `Y` Cantor, `m = 2`, `n = 3`. Then `3` is
invertible on `Z_2`, so every `Phi: BS(2,3) -> Homeo(X)` with `Phi(a) = a` kills `[t a t^-1, a]`.
- In `BS(2,3)` the normal closure of `[t a t^-1, a]` is exactly `ker(phi)` for the non-Hopfian surjection
  `phi: a -> a^2, t -> t`. Indeed, `psi: a -> t a t^-1 a^-1, t -> t` is a homomorphism from `BS(2,3)` to
  `G' = BS(2,3) / <<[t a t^-1, a]>>`: in `G'`, `u = t a t^-1` commutes with `a` and `u^2 = a^3`, so `c = u a^-1`
  satisfies `c^2 = a` and `t c^2 t^-1 = u = c^3`. Also `psi` and the map induced by `phi` are mutually inverse on
  generators, so `G' ≅ BS(2,3)`.
- Hence `Phi = Phi_1 o phi`, with `Phi_1(a) = Phi(t a t^-1 a^-1) = c`, a square root of the odometer `a`.
- Such a square root commutes with `a` and has no fixed fibre, since `2 delta = 1` has no solution in `Z_2`. It
  permutes the fibres by a free involution. A free involution of a Cantor space has a clopen fundamental domain, so
  `c` is again conjugate to `(+1) x id` on `K' x Y'`, with `K'` a pro-2 monothetic group on which `3` is invertible.
- Repeating gives `ker(Phi) ⊇ ker(phi^k)` for every `k`. This union is nontrivial, since `BS(2,3)` is non-Hopfian.
