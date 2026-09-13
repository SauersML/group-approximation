---
rg: 2
id: o2-central-sequence-k-theory-bi-cyclotomic-transfer
kind: claim
title: K-theory of the fixed central sequence algebra of an outer action on O_2 carries commuting dual actions of G and Ĝ whose norms vanish by transfer, and its fixed points on the unit class are strong approximate innerness of the action and of its dual
distinct_from:
  o2-rokhlin-iff-unit-vanishes-in-fixed-central-sequences: that proves the Rokhlin property is the vanishing of the unit class and introduces the Ĝ-action; this adds the dual G-action from the crossed product, proves both norm operators vanish, and reads the fixed points of both actions on the unit class dynamically.
  zp-restriction-trivial-splits-cellular-plus-phantom: that works in the ring KK^G(D, D) with the operators χ and θ; this works in K_* of a non-separable central sequence algebra, where the analogous operators are conjugations by eigen-isometries and by invariant implementing isometries.
  zp-o2-generator-kk-class-is-twisted-asymptotic-innerness: that splits KK^G(E, E) into Galois components where θ = χ^k and reads each through Gabe–Szabó uniqueness; this splits K_* of the fixed central sequence algebra over the same ring by transfer, and reads fixed points of the unit class by Cuntz comparison, with no uniqueness theorem.
---

**ESTABLISHED (derivation; standard inputs flagged in the proof; unreviewed).**
Let `G` be a finite abelian group, `A = O_2`, `α : G ↷ A` pointwise outer,
`B = A ⋊_α G` with dual action `α̂`, and
`F^α = (A_∞ ∩ A')^α`, which equals `(B_∞ ∩ B')^(α̂)` (item 3 of
`o2-rokhlin-iff-unit-vanishes-in-fixed-central-sequences`).  Put
`M_* = K_*(F^α)`.  It depends only on the exterior equivalence class of `α`.

1. **Two dual actions.**
   - (φ) For `χ ∈ Ĝ` let `v_χ ∈ A_∞ ∩ A'` be an isometry with
     `α_g(v_χ) = χ(g) v_χ`, and put `φ_χ = K_*(Ad v_χ)`.
   - (ψ) For `g ∈ G` there is an α-fixed isometry `y_g ∈ A_∞` with
     `a y_g = y_g α_g(a)` for all `a ∈ A`.  Each `x ↦ y_g x y_g*` maps `F^α`
     into itself; put `ψ_g = K_*(Ad y_g)`.  The `y_g u_g` are exactly the
     α̂-eigen-isometries of `B_∞ ∩ B'`.
   - Both are well-defined group actions on `M_*`.  They commute, so `M_*` is a
     `Z[Ĝ × G]`-module.  Replacing `α` by `α̂` exchanges `φ` and `ψ` and keeps
     `M_*` and `[1]`.
2. **Transfer: both norms vanish.**
   - `N_φ = Σ_(χ∈Ĝ) φ_χ = 0` on `M_*`, for every pointwise outer `α` on `O_2`.
     In particular `[Σ_g s_g s_g*] = 0` in `K_0(F^α)` for isometries `s_g` with
     orthogonal ranges and `α_h(s_g) = s_(hg)`.
   - If `O_2 ⋊_α G ≃_KK 0`, then `N_ψ = Σ_(g∈G) ψ_g = 0` on `M_*`.

   So for `G = Z/p` with contractible crossed product, `M_*` is a module over
   `Λ = Z[x, y]/(Φ_p(x), Φ_p(y)) ≅ Z[ζ_p] ⊗_Z Z[ζ_p]`, with `x = φ_(χ_0)`,
   `y = ψ_(g_0)` for generators `χ_0`, `g_0` with `χ_0(g_0) = ζ_p`.
3. **Fixed points on the unit class are strong approximate innerness.**
   For `(λ, h) ∈ Ĝ × G` the following are equivalent:
   - `φ_λ ψ_h [1] = [1]` in `K_0(F^α)`;
   - there is a unitary `w ∈ A_∞` with `α_g(w) = λ(g) w` and `w* a w = α_h(a)`
     for all `a ∈ A`.

   For `λ = 1` this says `α_h` is strongly approximately inner, with unitaries in
   `O_2^α`.  For `h = 1` it says `α̂_(λ̄)` is strongly approximately inner.  Also
   `α` is Rokhlin iff `[1] = 0` iff `M_* = 0`.
4. **What transfer alone gives, and where it stops** (`G = Z/p`, contractible
   crossed product).
   - If `α` is strongly approximately inner, then `(1 − y)[1] = 0` and
     `N_ψ[1] = 0`, so `p[1] = 0`.  Izumi's theorem (Izumi I, Theorem 4.6, via
     `izumi-rokhlin-approximately-representable-duality` and
     `outer-actions-on-o2-kk-g-contractible-iff-rokhlin` item 4) gives `[1] = 0`.
     So transfer recovers Izumi's conclusion up to `p`-torsion.
   - Transfer cannot finish alone: the free module `Λ` with the element `1`
     satisfies every relation of item 2, and `1 ≠ 0`.
   - After inverting `p`, `Λ[1/p] ≅ ∏_(k∈(Z/p)^×) Z[ζ_p, 1/p]`, with `y = x^k`
     on the `k`-th factor.  The factors are the `p − 1` lines of `Ĝ × G` on
     which the form `q(λ, h) = λ(h)` is anisotropic.  The two isotropic lines,
     `Ĝ × 0` and `0 × G`, are what the two transfers kill.  If item 3 holds
     for `(λ, h) = (χ_0^(−k), g_0)`, the image of `[1]` in `M_0[1/p]` lies in
     the `k`-th factor.

**How the transfer avoids the Baaj–Skandalis trap.**  The Attempts on
`zp-restriction-and-crossed-product-detect-kk-g-contractibility` note that the
hypotheses `Res D ≃ 0` and `D ⋊ G ≃ 0` are exchanged by duality, so no
asymmetry is available.  The transfer does not look for one.
- It turns each hypothesis into one operator identity on the same group `M_*`:
  `N_φ = 0` comes from `A ≅ O_2`, and `N_ψ = 0` from `B ≅ O_2`.
- Duality swaps the two identities, and fixes the target `[1] = 0`.
- The identities meet in the ring `Λ`, which neither alone generates.  Item 4
  shows the combination is strictly stronger than either factor.
- What remains must be non-formal input about `[1]`.  The known inputs, Izumi's
  theorem and its dual, are themselves a swapped pair: `(1 − y)[1] = 0 ⟹ [1] = 0`
  and `(1 − x)[1] = 0 ⟹ [1] = 0`.

**Consequence for detection.**  By
`outer-actions-on-o2-kk-g-contractible-iff-rokhlin` item 3, detection at `p`
says: for every outer `α : Z/p ↷ O_2` with contractible crossed product, the
Λ-module `M_*` is zero.  The isotropic transfers already hold.  An open core is
`[1]` itself and its `p − 1` anisotropic components.  By item 3 these are the
twisted forms of strong approximate innerness, with `λ(h) ≠ 1`.

**Model tests.**
- Rokhlin model `id ⊗ μ_G`: `M_* = 0`.  All unitaries in item 3 exist, one
  far-out tensor factor of `M_(p^∞)` at a time.
- Trivial action on `O_2`: excluded by outerness.  There are no eigen-isometries
  for `χ ≠ 1`, so `φ` is undefined.
- Outer action whose crossed product `B` is not `O_2`: the second transfer
  has no input.  `B` is a unital Kirchberg algebra with `[1] ≠ 0` in
  `K_0(B_∞ ∩ B')`, since `[1] = 0` there would embed `O_2` centrally and force
  `B ≅ O_2`.

No priority is claimed for items 1(φ) and 3 at `λ = 1`, `h = 1`.  Items 1(ψ), 2
and 4 were not found in the predecessor nodes or in the sources those nodes
cite.  The bounded check covered Izumi I as cited through Barlak–Li and
Gabe–Szabó, not the wider literature.

Proof: `o2-central-sequence-k-theory-bi-cyclotomic-transfer-proof`.
