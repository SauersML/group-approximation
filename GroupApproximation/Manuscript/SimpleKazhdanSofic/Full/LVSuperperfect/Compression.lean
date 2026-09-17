import GroupApproximation.Leavitt.LeavittCorner

/-!
# The compression identity `w · c(u) · w⁻¹ = c(c(u))` (Khanh, Prop. 3.2)

Let `A` be a ring with a binary Leavitt family `s₀, s₁, t₀, t₁`
(`t_i s_j = δ_ij`, `s₀t₀ + s₁t₁ = 1`).  The compression
`c(u) = s₁t₁ + s₀ u t₀` is the unit-group homomorphism `LeavittFamily.compressedHom`
(`Leavitt/LeavittCorner.lean`).  Khanh (arXiv:2609.08428, proof of Prop. 3.2) observes that `c` and
`c ∘ c` are conjugate by one fixed unit

  `w = s₀s₀t₀ + s₀s₁t₀t₁ + s₁t₁t₁`, with `w⁻¹ = s₀t₀t₀ + s₁s₀t₁t₀ + s₁s₁t₁`,

so `c` induces an idempotent map on group homology.  Combined with local nilpotence (from
`K_*(L) = 0`), this gives the vanishing of homology used for the superperfectness of `Lˣ`
(`simple_kazhdan_sofic_group.tex` l.733-735, binder `hsp`).

This file proves the ring identities for an arbitrary `LeavittFamily`:

* `compressionConjUnit L : Aˣ`, the unit `w` with its explicit inverse.
* `compressionConjUnit_mul_compressedHom_mul_inv`: `w * c u * w⁻¹ = c (c u)`.
* `conj_comp_compressedHom`: `conj w ∘ c = c ∘ c` as monoid homomorphisms.
* `map_compressedHom_compressedHom`: every homomorphism `F : Aˣ →* M` to a commutative group
  satisfies `F (c (c u)) = F (c u)`.  This is the degree-one case of idempotence.
-/

set_option linter.unusedSimpArgs false

namespace GroupApproximation.Full.LVSuperperfect

variable {A : Type*} [Ring A] (L : LeavittFamily A)

/-- The compression as an explicit value: `c(u) = s₁t₁ + s₀ u t₀`. -/
theorem compressedHom_val (u : Aˣ) :
    ((L.compressedHom u : Aˣ) : A) = L.s1 * L.t1 + L.s0 * (u : A) * L.t0 :=
  rfl

/-- **Khanh's conjugating unit** `w = s₀s₀t₀ + s₀s₁t₀t₁ + s₁t₁t₁`, with inverse
`s₀t₀t₀ + s₁s₀t₁t₀ + s₁s₁t₁` (arXiv:2609.08428, proof of Prop. 3.2). -/
def compressionConjUnit : Aˣ where
  val := L.s0 * L.s0 * L.t0 + L.s0 * L.s1 * L.t0 * L.t1 + L.s1 * L.t1 * L.t1
  inv := L.s0 * L.t0 * L.t0 + L.s1 * L.s0 * L.t1 * L.t0 + L.s1 * L.s1 * L.t1
  val_inv := by
    have h : (L.s0 * L.s0 * L.t0 + L.s0 * L.s1 * L.t0 * L.t1 + L.s1 * L.t1 * L.t1) *
        (L.s0 * L.t0 * L.t0 + L.s1 * L.s0 * L.t1 * L.t0 + L.s1 * L.s1 * L.t1) =
        L.s0 * (L.s0 * L.t0 + L.s1 * L.t1) * L.t0 + L.s1 * L.t1 := by
      simp [add_mul, mul_add, mul_assoc, add_assoc]
    exact h.trans (by rw [L.sum_range, mul_one, L.sum_range])
  inv_val := by
    have h : (L.s0 * L.t0 * L.t0 + L.s1 * L.s0 * L.t1 * L.t0 + L.s1 * L.s1 * L.t1) *
        (L.s0 * L.s0 * L.t0 + L.s0 * L.s1 * L.t0 * L.t1 + L.s1 * L.t1 * L.t1) =
        L.s0 * L.t0 + L.s1 * (L.s0 * L.t0 + L.s1 * L.t1) * L.t1 := by
      simp [add_mul, mul_add, mul_assoc, add_assoc]
    exact h.trans (by rw [L.sum_range, mul_one, L.sum_range])

theorem compressionConjUnit_val :
    ((compressionConjUnit L : Aˣ) : A) =
      L.s0 * L.s0 * L.t0 + L.s0 * L.s1 * L.t0 * L.t1 + L.s1 * L.t1 * L.t1 :=
  rfl

/-- **Khanh, Prop. 3.2 (ring identity).**  `w · c(u) = c(c(u)) · w`, i.e. both sides equal
`s₀s₀ u t₀ + s₀s₁t₀t₁ + s₁t₁t₁`. -/
theorem compressionConjUnit_mul_compressedHom (u : Aˣ) :
    compressionConjUnit L * L.compressedHom u =
      L.compressedHom (L.compressedHom u) * compressionConjUnit L := by
  apply Units.ext
  simp only [Units.val_mul, compressedHom_val, compressionConjUnit_val]
  simp [add_mul, mul_add, mul_assoc, add_assoc, add_comm, add_left_comm]

/-- **Khanh, Prop. 3.2.**  `w · c(u) · w⁻¹ = c(c(u))`: the compression and its square differ by
an inner automorphism. -/
theorem compressionConjUnit_mul_compressedHom_mul_inv (u : Aˣ) :
    compressionConjUnit L * L.compressedHom u * (compressionConjUnit L)⁻¹ =
      L.compressedHom (L.compressedHom u) := by
  rw [mul_inv_eq_iff_eq_mul]
  exact compressionConjUnit_mul_compressedHom L u

/-- `conj w ∘ c = c ∘ c` as homomorphisms `Aˣ →* Aˣ`. -/
theorem conj_comp_compressedHom :
    (MulAut.conj (compressionConjUnit L)).toMonoidHom.comp L.compressedHom =
      L.compressedHom.comp L.compressedHom := by
  apply MonoidHom.ext
  intro u
  show compressionConjUnit L * L.compressedHom u * (compressionConjUnit L)⁻¹ =
    L.compressedHom (L.compressedHom u)
  exact compressionConjUnit_mul_compressedHom_mul_inv L u

/-- **Idempotence in degree one.**  A homomorphism to a commutative group cannot distinguish
`c ∘ c` from `c`. -/
theorem map_compressedHom_compressedHom {M : Type*} [CommGroup M] (F : Aˣ →* M) (u : Aˣ) :
    F (L.compressedHom (L.compressedHom u)) = F (L.compressedHom u) := by
  rw [← compressionConjUnit_mul_compressedHom_mul_inv L u, map_mul, map_mul, map_inv,
    mul_comm (F (compressionConjUnit L)) (F (L.compressedHom u)), mul_inv_cancel_right]

end GroupApproximation.Full.LVSuperperfect
