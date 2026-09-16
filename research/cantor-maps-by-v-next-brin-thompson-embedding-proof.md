---
rg: 2
id: cantor-maps-by-v-next-brin-thompson-embedding-proof
kind: route
title: "Direct proof: fibre the Γ-action over the first Cantor coordinate"
target: cantor-maps-by-v-embed-in-next-brin-thompson-group
requires: []
artifacts:
  - research/artifacts/cantor-maps-by-v-in-brin-thompson-2026-09-16.md
---

Write `C^{n+1} = C × C^n`, and define `Φ(f)(x,p) = (x, f(x)(p))` and
`Φ(h)(x,p) = (hx, p)`.

1. **`Φ(h) ∈ (n+1)V`.** If `h` maps `[v_j]` canonically to `[v'_j]`, then `Φ(h)`
   maps the bricks `[v_j] × C^n` canonically to `[v'_j] × C^n`.
2. **`Φ(f) ∈ (n+1)V`.** `f` is constant, equal to `γ_i`, on the leaves `[w_i]` of a
   complete prefix code. If `γ_i` maps the bricks `B_{ij}` of a partition of `C^n`
   canonically to `B'_{ij}`, then `Φ(f)` maps `[w_i] × B_{ij}` canonically onto
   `[w_i] × B'_{ij}`, with the trivial prefix replacement in the first coordinate.
   These bricks partition `C^{n+1}`.
3. **Relations.** Pointwise computation gives:
   - `Φ(f)Φ(f') = Φ(ff')`;
   - `Φ(h)Φ(h') = Φ(hh')`;
   - `Φ(h)Φ(f)Φ(h)^{-1}(x,p) = (x, f(h^{-1}x)(p)) = Φ(h·f)(x,p)`.

   So `Φ(f,h) := Φ(f)Φ(h)` respects the product
   `(f,h)(f',h') = (f·(h·f'), hh')`.
4. **Injectivity.** `Φ(f,h)(x,p) = (hx, f(hx)(p))`. If this is the identity, then
   `h = 1`, and then `f(x) = 1` for all `x`.

For the corollaries:

- `C(C,Z) ⋊ V ≤ 2V`: take `Γ = ⟨s⟩` with `s ∈ V = 1V` of infinite order.
- `C(C,V) ⋊ V ≤ 2V`: take `Γ = V = 1V`.

The artifact §2 writes the details out.
