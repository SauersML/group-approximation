---
rg: 2
id: actor-extension-lifts-vertex-rounding-to-the-laurent-vertex
kind: claim
title: At trace-preserving Kun--Thom actor models with d = 3 and r >= 6, vertex rounding lifts to Laurent-vertex rounding, because SL_3(Z) transport and property (T) of Z^3 x| SL_3(Z) kill the K_2 symbol twists
distinct_from:
  laurent-vertex-rounds-for-every-model: that is Laurent-vertex rounding at every actor model, open; this proves it follows at a given actor model from polynomial-vertex rounding there, for d = 3 and r >= 6, closing the St_r(L) to Delta descent that node records as open.
  hs-stable-vertex-rounding-for-every-model: that is (H1), open; this proves that at actor models (H1) already implies the stronger Laurent rounding, so for d = 3, r >= 6 the two are equivalent.
  unit-type-vertex-rounding-agrees-with-sigma-on-laurent-steinberg: that gives agreement on the Steinberg cover; this descends to Delta by showing the central K_2 characters of the rounding concentrate at 1.
  compressor-transport-exactifies-under-vertex-rounding: that transports root spectra of the vertex; this transports central characters of the Laurent Steinberg extension, on the Laurent K_2.
artifacts:
  - research/artifacts/hs-extension-laurent-descent-2026-09-13.md
---

**ESTABLISHED (unreviewed).** Let `Γ = EL_r(F_q[x_1, x_2, x_3]) < Δ = EL_r(F_q[x^(±1)]) < G = Δ ⋊ SL_3(Z)`, with
`r >= 6`. Let `σ : G -> U(prod_U M_n)` be trace-preserving and satisfy (H1) on `Γ`. Then `σ|Δ` rounds to genuine
representations of `Δ`.

**The obstruction removed.** A unit-type rounding extends to `St_r(L)` in agreement with `σ`
(`unit-type-vertex-rounding-agrees-with-sigma-on-laurent-steinberg`). Its irreducible constituents carry central
characters `ω` on

```text
K = K_2(r, L) ≅ K_2(L) ≅ (F_q^×)^3 ⊕ Λ²Z^3,     r >= d + 3 = 6.
```

This uses injective stability and the fundamental theorem, as imported on main. The characters satisfy
`∫|ω(k) - 1|^2 -> 0`, but they may have unbounded `p`-power order. So the rounding need not factor through `Δ` a
priori. Those are the symbol twists.

**Proof sketch** (artifact §§2–3).
1. **Unit type.** By the per-model chain, the rounding is of unit type off vanishing trace.
2. **Agreement.** `σ∘q = ρ'` on `St_r(L)`.
3. **Torsion.** On the torsion symbols `{u_0, x_i}`, a nontrivial value is a `(q-1)`-th root of unity. So the mass of
   characters nontrivial on the torsion tends to `0`.
4. **Transport.** For the nonnegative generators `I + E_ij` of `SL_3(Z)`, compressor transport is exact off trace
   `η_n -> 0` by property (T) of `Γ`. The same intertwiner intertwines the canonical Laurent extensions, since
   `x^(-c) = x^((m_n - 1)c)` in `A_n`. So the character distribution `ν_n` is total-variation almost invariant under
   `ω -> ω∘φ_M`.
5. **Property (T) on the symbols.** In `ℓ²` of the dual of `Λ²Z^3 ≅ (Z^3)^*`, the vector `√ν_n` is almost invariant
   under `SL_3(Z) ⋉ Λ²Z^3 ≅ Z^3 ⋊ SL_3(Z)`, which has property (T)
   (`affine-semidirect-sl3-source-has-property-t`). So `ν_n` concentrates at `ω = 1` in total variation.
6. **Descend.** The constituents with trivial central character carry trace `-> 1` and factor through `Δ`.

**Consequences.**
- **What extension buys.** At actor models, rounding of the polynomial vertex, rounding of the Laurent vertex, and
  unit-type rounding are equivalent (`d = 3`, `r >= 6`). In particular `laurent-vertex-rounds-for-every-model` at those
  parameters is equivalent to the Theorem E instance of (H1).
- **Why the twists die.** The Deligne-type symbol twists that could separate the two conditions are killed by the
  `SL_3(Z)`-symmetry of the actor, through property (T) of the affine group.
- **Scope.**
  - `d >= 4` needs relative (T) for `(SL_d(Z) ⋉ Λ²Z^d, Λ²Z^d)` and `r >= d + 3`; this is not checked.
  - `r <= 5` is outside stability.
  - The Bowen–Chapman parameters `(2, 3, 3)` are not covered.
- **Conditional.** Nothing here produces a rounding.

Derivation: `actor-extension-lifts-vertex-rounding-proof`.
