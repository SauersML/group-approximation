import Mathlib

/-!
# The transverse local model at the mapping-torus zero

Lane `found-euler-class`, campaign target 3 (STW Problem LIX).

The counterexample manuscript
`research/artifacts/stw59-simple-ah-k1-counterexample-manuscript-2026-09-05.md`,
proof of Lemma 2, forms over `S¹ × M` the mapping-torus bundle `W_g` and exhibits
the section

```text
S (x, y, t) = ((1 - t) • e₃ + t • x, χ t • σ y)
```

of `V = 1³ ⊕ H`.  Its `ℂ³`-component vanishes exactly at `t = 1/2`, `x = -e₃`, and
the manuscript asserts that at that point the derivative of the `ℂ³`-component is
the **real-linear isomorphism**

```text
T_{-e₃} S⁵ ⊕ ℝ → ℂ³,    (ξ, a) ↦ ξ/2 - 2 a e₃.
```

This file proves that assertion, in the only generality it is ever used: `E` a real
inner product space (the realification of `ℂ³`), `v` a unit vector (`e₃`), and
`T_{-v} S(E) = (ℝ ∙ v)ᗮ` the tangent space of the unit sphere at `-v`.  Nothing here
depends on the ambient bundle, on smoothness, or on any orientation: the statement is
that a certain explicit real-linear map is bijective.

## Why this file carries no orientation data

The campaign's contradiction is a **parity** contradiction (`±1` against an even
integer), so the Euler/zero-count half of the obstruction only ever needs the local
index *mod 2*.  A transverse zero has local index `±1`, and mod `2` that is `1`
as soon as the derivative is invertible — the sign, and therefore every orientation
of `E`, of `T_{-v} S(E) ⊕ ℝ`, and of the bundle, is irrelevant.  `eulerLocalModelEquiv`
below is exactly the input that a mod-2 local index needs, and no more.

## Main results

* `eulerLocalModel_deriv_eq` — the displayed map really is the derivative of the
  `ℂ³`-component of the manuscript's section at `(x, t) = (-v, 1/2)`, as an identity
  between the two expressions.
* `eulerLocalModel_eq_zero` / `eulerLocalModel_surjective` — the kernel and image
  statements.
* `eulerLocalModelEquiv` — the bundled conclusion: `(ℝ ∙ v)ᗮ × ℝ ≃ₗ[ℝ] E`.
-/

noncomputable section

namespace GroupApproximation.AlgTop

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ## 1. The map, and its identification with the manuscript's derivative -/

/-- The manuscript's derivative at the transverse zero, as a real-linear map
`T_{-v} S(E) ⊕ ℝ → E`, `(ξ, a) ↦ ξ/2 - 2 a v`.  The tangent space to the unit sphere
at `-v` is the orthogonal complement `(ℝ ∙ v)ᗮ`. -/
def eulerLocalModel (v : E) : (((ℝ ∙ v)ᗮ) × ℝ) →ₗ[ℝ] E where
  toFun p := (2 : ℝ)⁻¹ • (p.1 : E) - (2 * p.2) • v
  map_add' p q := by
    simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add]
    module
  map_smul' c p := by
    simp only [Prod.smul_fst, Prod.smul_snd, SetLike.val_smul, smul_eq_mul, RingHom.id_apply]
    module

@[simp]
theorem eulerLocalModel_apply (v : E) (p : ((ℝ ∙ v)ᗮ) × ℝ) :
    eulerLocalModel v p = (2 : ℝ)⁻¹ • (p.1 : E) - (2 * p.2) • v := rfl

/-- **The map is the manuscript's derivative.**  The `ℂ³`-component of the section
`S` is `f (x, t) = (1 - t) • v + t • x`; its derivative at `(x, t)` in the direction
`(ξ, a)` is `t • ξ + a • (x - v)`.  At the zero `x = -v`, `t = 1/2` this is exactly
`ξ/2 - 2 a v`. -/
theorem eulerLocalModel_deriv_eq (v ξ : E) (a : ℝ) :
    ((2 : ℝ)⁻¹) • ξ + a • ((-v) - v) = (2 : ℝ)⁻¹ • ξ - (2 * a) • v := by
  module

/-! ## 2. Injectivity -/

/-- The kernel of the local model is trivial, in unbundled form: if `ξ` is tangent to
the sphere at `-v` (equivalently `ξ ⊥ v`) and `ξ/2 = 2 a v`, then `ξ = 0` and `a = 0`. -/
theorem eulerLocalModel_eq_zero_aux {v ξ : E} {a : ℝ} (hv : ‖v‖ = 1)
    (hξ : ⟪v, ξ⟫_ℝ = 0) (h : (2 : ℝ)⁻¹ • ξ - (2 * a) • v = 0) :
    ξ = 0 ∧ a = 0 := by
  have hvv : ⟪v, v⟫_ℝ = 1 := by
    rw [real_inner_self_eq_norm_sq, hv, one_pow]
  -- Pair the relation with `v`: the tangential part drops out and `2 a = 0`.
  have hpair : (2 : ℝ)⁻¹ * ⟪v, ξ⟫_ℝ - (2 * a) * ⟪v, v⟫_ℝ = 0 := by
    have hc := congrArg (fun w : E => ⟪v, w⟫_ℝ) h
    simpa only [inner_sub_right, real_inner_smul_right, inner_zero_right] using hc
  have ha : a = 0 := by
    rw [hξ, hvv] at hpair
    linarith
  refine ⟨?_, ha⟩
  have h2 : (2 : ℝ)⁻¹ • ξ = 0 := by
    rw [ha] at h
    simpa using h
  have hne : (2 : ℝ)⁻¹ ≠ (0 : ℝ) := by norm_num
  exact (smul_eq_zero.mp h2).resolve_left hne

theorem eulerLocalModel_eq_zero {v : E} (hv : ‖v‖ = 1) {p : ((ℝ ∙ v)ᗮ) × ℝ}
    (h : eulerLocalModel v p = 0) : p = 0 := by
  obtain ⟨ξ, a⟩ := p
  have hξ : ⟪v, (ξ : E)⟫_ℝ = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp ξ.2
  have h' : (2 : ℝ)⁻¹ • (ξ : E) - (2 * a) • v = 0 := h
  obtain ⟨h1, h2⟩ := eulerLocalModel_eq_zero_aux hv hξ h'
  have hξ0 : ξ = 0 := Subtype.ext h1
  rw [hξ0, h2]
  rfl

theorem eulerLocalModel_injective {v : E} (hv : ‖v‖ = 1) :
    Function.Injective (eulerLocalModel v) := by
  intro p q hpq
  have h : eulerLocalModel v (p - q) = 0 := by
    rw [map_sub, hpq, sub_self]
  exact sub_eq_zero.mp (eulerLocalModel_eq_zero hv h)

/-! ## 3. Surjectivity -/

/-- Every vector of `E` is `ξ/2 - 2 a v` for a tangential `ξ` and a real `a`: split
`w` into its `v`-component and its orthogonal part. -/
theorem eulerLocalModel_surjective_aux {v : E} (hv : ‖v‖ = 1) (w : E) :
    ∃ (ξ : E) (a : ℝ), ⟪v, ξ⟫_ℝ = 0 ∧ (2 : ℝ)⁻¹ • ξ - (2 * a) • v = w := by
  have hvv : ⟪v, v⟫_ℝ = 1 := by
    rw [real_inner_self_eq_norm_sq, hv, one_pow]
  refine ⟨(2 : ℝ) • (w - (⟪v, w⟫_ℝ) • v), -((⟪v, w⟫_ℝ) / 2), ?_, ?_⟩
  · rw [real_inner_smul_right, inner_sub_right, real_inner_smul_right, hvv]
    ring
  · have hs : (2 : ℝ)⁻¹ • ((2 : ℝ) • (w - (⟪v, w⟫_ℝ) • v)) = w - (⟪v, w⟫_ℝ) • v := by
      rw [smul_smul]
      norm_num
    have hc : (2 : ℝ) * -((⟪v, w⟫_ℝ) / 2) = -(⟪v, w⟫_ℝ) := by ring
    rw [hs, hc, neg_smul, sub_neg_eq_add, sub_add_cancel]

/-- The bundled surjectivity statement. -/
theorem eulerLocalModel_surjective {v : E} (hv : ‖v‖ = 1) :
    Function.Surjective (eulerLocalModel v) := by
  intro w
  obtain ⟨ξ, a, hξ, hw⟩ := eulerLocalModel_surjective_aux hv w
  have hmem : ξ ∈ (ℝ ∙ v)ᗮ := Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hξ
  exact ⟨(⟨ξ, hmem⟩, a), hw⟩

/-! ## 4. The conclusion -/

/-- **The manuscript's local model is a real-linear isomorphism.**
`T_{-v} S(E) ⊕ ℝ ≃ₗ[ℝ] E`, `(ξ, a) ↦ ξ/2 - 2 a v`.

This is the statement a mod-2 local index at the mapping-torus zero consumes: the
derivative is invertible, so the zero is transverse and its local index is odd.  No
orientation and no sign is computed, because none is needed for a parity count. -/
def eulerLocalModelEquiv {v : E} (hv : ‖v‖ = 1) : (((ℝ ∙ v)ᗮ) × ℝ) ≃ₗ[ℝ] E :=
  LinearEquiv.ofBijective (eulerLocalModel v)
    ⟨eulerLocalModel_injective hv, eulerLocalModel_surjective hv⟩

@[simp]
theorem eulerLocalModelEquiv_apply {v : E} (hv : ‖v‖ = 1) (p : ((ℝ ∙ v)ᗮ) × ℝ) :
    eulerLocalModelEquiv hv p = (2 : ℝ)⁻¹ • (p.1 : E) - (2 * p.2) • v := rfl

end GroupApproximation.AlgTop
