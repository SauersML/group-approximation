---
rg: 2
id: brick-diagonal-ascending-hnn-embedding-proof
kind: route
title: Push the code digit into a fresh coordinate; the pushing map conjugates h x id to its brick diagonal, and the fresh coordinate separates the stable letter
target: brick-diagonal-ascending-hnns-embed-in-brin-thompson-groups
requires:
  - renormalizable-thompson-elements-give-baumslag-solitar
---

Notation as in the claim. Fix a complete prefix code `c_0, …, c_{m-1}` of `C` (all words nonempty,
for example `1^i 0` for `i < m-1` and `1^{m-1}`).

**Step 1. `δ_e(h) ∈ kV`.** On `X_i`, `e_i h e_i^{-1}` is a composite of brick-local homeomorphisms,
hence brick-local on a finite brick partition of `X_i`. The pieces `X_i` partition `X`, so the union
is a brick-local homeomorphism of `X`, i.e. an element of `kV`. Multiplicativity is pointwise:
`e_i h h' e_i^{-1} = (e_i h e_i^{-1})(e_i h' e_i^{-1})`. Injectivity: `h = e_0^{-1} δ_e(h) e_0`.

**Step 2. The conjugator.** Define `g: X × C -> X × C` by `g(e_i x, y) = (x, c_i y)`.
- It is a bijection: every point is `(e_i x, y)` for unique `i, x, y`. The level `X_i × C` goes onto
  `X × c_i C`, and the cones `c_i C` partition `C`.
- It lies in `(k+1)V`: on `X_i × C` it is `e_i^{-1}` (brick-local) in the first `k` coordinates and
  the prefix insertion `ε ↦ c_i` in the last.

**Step 3. The relation.** For `h ∈ kV`:
`g (δ_e(h) × id) g^{-1} (x, c_i y) = g(δ_e(h) e_i x, y) = g(e_i h x, y) = (h x, c_i y)`.
So `g (δ_e(h) × id) g^{-1} = h × id`, that is, `g^{-1} (h × id) g = δ_e(h) × id`.
The assignment `h ↦ h × id`, `t ↦ g` therefore respects `t^{-1} h t = δ_e(h)` for `h ∈ H`, and
defines `Φ: H *_{δ_e} -> (k+1)V`.

**Step 4. Normal form.** In `H *_{δ_e}` we have `h t = t δ_e(h)` and `t^{-1} h = δ_e(h) t^{-1}`. So
every positive `t` can be moved left and every `t^{-1}` right, and every element equals
`t^a h t^{-b}` with `a, b >= 0` and `h ∈ H`. This is the usual structure `H *_δ = L ⋊ ⟨t⟩`, with
`L = ⋃_n t^n H t^{-n}`.

**Step 5. Injectivity.** Suppose `Φ(t^a h t^{-b}) = g^a (h × id) g^{-b} = 1`. Then `h × id = g^{b-a}`.
- If `n = b - a > 0`: `g^n (x, y) = (x', w(x) y)`, where `w(x)` is a concatenation of `n` nonempty code
  words. For fixed `x`, `w(x) y = y` only at `y = w(x)^∞`. But `h × id` fixes the last coordinate
  of every point, so `h × id ≠ g^n`. The case `n < 0` follows by inverting.
- So `a = b`, `h × id = 1`, and `h = 1`. Hence `Φ` is injective.

**Step 6. Corollaries.**
- (1) `δ_e ρ` and `ρ φ` are homomorphisms that agree on generators, so `δ_e(ρ G) = ρ(φ G) ⊆ ρ G`.
  Apply the theorem to `H = ρ(G)`, and note `ρ(G) *_{δ_e} ≅ G *_φ`. The host `(k+1)V` is
  finitely presented and simple (Brin; Hennig–Matucci), so `G *_φ` embeds in a finitely presented
  simple group.
- (2) `H = kV`.
- (3) Write `e_i = ê_i π`. Then `δ_e(h) = ⊔ ê_i (π h π^{-1}) ê_i^{-1}`, and `π` normalizes `kV`.
  The same `g` satisfies `g = (π^{-1} × id) g_0` with `g_0(ê_i x', y) = (x', c_i y) ∈ (k+1)V`.
  Steps 3–5 never look at the first `k` coordinates, so they go through unchanged in
  `(k+1)V ⋊ Sym(k)`.
- (4) `T^m e_i = e_i T` for an odometer (`renormalizable-thompson-elements-are-odometer-codes`, item
  3(c)), so `δ_e(T) = T^m`. `⟨T⟩ *_{×m} = BS(1,m)`. ∎
