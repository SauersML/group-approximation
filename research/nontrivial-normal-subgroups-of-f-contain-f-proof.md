---
rg: 2
id: nontrivial-normal-subgroups-of-f-contain-f-proof
kind: route
title: A displaced dyadic interval puts all commutators of its rigid stabilizer into N, and two overlapping commutators satisfy Brin's one-sided approach criterion
target: nontrivial-normal-subgroups-of-thompson-f-contain-a-copy-of-f
requires:
  - brin-plo-i-one-sided-approach-gives-a-copy-of-f
---

Conventions: maps compose right to left, and `[a,b] = a b a^{-1} b^{-1}`. The support
`supp f` is the open set of points moved by `f`. Elements with disjoint supports
commute, and `supp(g f g^{-1}) = g(supp f)`.

**One-bump elements.** Let `x_0(t) = t/2` on `[0,1/2]`, `t − 1/4` on `[1/2,3/4]`, and
`2t − 1` on `[3/4,1]`. Then `x_0 ∈ F` and `x_0(t) < t` on `(0,1)`. Take dyadic `c`
and `d = c + 2^{-k}`. Define `b_{c,d}(t) = c + 2^{-k} x_0(2^k(t − c))` on `[c,d]`, and
`t` elsewhere.

- `b_{c,d}` has breakpoints `c`, `c + 2^{-k-1}`, `c + 3·2^{-k-2}` and `d`, and slopes
  in `{1/2, 1, 2}`. So it lies in `F`.
- `b_{c,d}(t) < t` on `(c,d)`. So for `e ≠ 0` the element `b_{c,d}^e` has exactly one
  orbital, `(c,d)`.

For an open interval `J`, write `F_J = {f ∈ F : supp f ⊆ J}`.

**Step 1 (the commutator trick).** Take `1 ≠ g ∈ N`, and a point `t_0` with
`g(t_0) ≠ t_0`. By continuity there is an open `U ∋ t_0` with `g(Ū) ∩ Ū = ∅`. Choose
a dyadic interval `J = (p, q) ⊆ U` of length `2^{-r}`. Let `h, k ∈ F_J`, and put
`a = g h^{-1} g^{-1}`.

- `supp a ⊆ g(J)`, which is disjoint from `J`. So `a` commutes with `h`, with `k`, and
  with every element of `F_J`.
- Hence `[g, h^{-1}] = a h`, and
  `[a h, k] = a h k h^{-1} a^{-1} k^{-1} = a (h k h^{-1} k^{-1}) a^{-1} = [h,k]`.
- `N` is normal and `g ∈ N`, so `[g, h^{-1}] ∈ N` and then `[[g,h^{-1}], k] ∈ N`.

Therefore `[h,k] ∈ N` for all `h, k ∈ F_J`.

**Step 2 (two commutators).** Put `h = b_{p,q}^{-1}`, so `h(t) > t` on `J`. Choose a
dyadic `s ∈ J` and `δ = 2^{-k}` with `s ∈ δZ` and `s + 3δ < h(s)`. This is possible:
fix `s`, then take `k` large. Let `k_1 = b_{s, s+2δ}` and `k_2 = b_{s+δ, s+3δ}`, both in
`F_J`. Put `c_1 = [h, k_1] = (h k_1 h^{-1}) k_1^{-1}` and `c_2 = [h, k_2]`. Both lie in
`N` by Step 1.

- `h k_1 h^{-1}` has the single orbital `(h(s), h(s+2δ))`, and `k_1^{-1}` has the single
  orbital `(s, s+2δ)`.
- These are disjoint, since `h(s) > s + 3δ`. So the orbitals of `c_1` are exactly these
  two intervals.
- Likewise the orbitals of `c_2` are `(s+δ, s+3δ)` and `(h(s+δ), h(s+3δ))`.

**Step 3 (Brin).** Let `H = ⟨c_1, c_2⟩ ≤ N`. Its fixed point set is
`Fix(c_1) ∩ Fix(c_2)`, so its support is the union of the four orbitals above:
`(s, s+3δ) ∪ (h(s), h(s+3δ))`. The two pieces have disjoint closures because
`h(s) > s + 3δ`. So `(s, s+3δ)` is an orbital of `H`.

- The only orbital of `c_1` lying in `(s, s+3δ)` is `(s, s+2δ)`. It has `s` as an
  endpoint and does not have `s + 3δ` as an endpoint.
- So `c_1` approaches `s` in `(s, s+3δ)` but not `s + 3δ`, in Brin's sense.
- By Brin's Theorem 1, `H` contains a subgroup isomorphic to `F`, and `H ≤ N`.

**Consequence.** `F_0 ∩ N ◁ F_0 ≅ F`. If it is trivial, then `F_0 → G/N` is
injective. Otherwise it contains a copy of `F` by the above. ∎
