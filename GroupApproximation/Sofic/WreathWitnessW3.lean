import GroupApproximation.Sofic.AscendingHNNStabilizer
import GroupApproximation.Sofic.CollapseUniverseScopeDefs
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Why `(W3)` is a hypothesis and not a consequence

`non_mf_groups_exist.tex`, `rem:collapse-finite-stage`, last paragraph (grep
`"is essential"`, never a line number: the file is edited concurrently):

> The commutation hypothesis `(W3)` is essential: it gives the joint spectral
> calculus behind the rank identity of Step 2.  Anticommuting Clifford
> coordinates have no joint spectral labels; their collapse mechanism is the
> central sign of `thm:A`.

Read literally, that is not a claim that `D_coll(L,s) ≤ Res_MF(H)` becomes
false without `(W3)`: `D_coll(L,s)` is *defined* by quantifying over witnesses,
so deleting `(W3)` changes the object rather than the theorem, and the last
clause says the anticommuting case is handled by a different mechanism — the
central sign of `thm:A` — rather than failing.  So there is no counterexample
to state, and this module does not invent one.

What the remark does assert, and what is proved here, is that `(W3)` is an
independent condition rather than a consequence of `(W1)` and `(W2)`, and that
the Clifford configuration of the manuscript's own construction is exactly
where it fails.  Two statements:

* `not_commute_of_anticommute`: two anticommuting involutions of a ring in
  which `1 + 1 ≠ 0` do not commute.  This is the algebraic content of "have no
  joint spectral labels": a joint spectral calculus is available precisely for
  commuting operators, and anticommutation forbids commutation outright.
* `cliffordCoordinates_fail_W3`: in the Kazhdan--Clifford ambient group, the
  moved root lamp `d = t c t⁻¹` satisfies `(W1)` and `(W2)` for the base copy
  compressed by `t`, and fails `(W3)`; the obstruction is *precisely* the
  central Clifford sign, since the failing commutator is the marked word of
  `thm:A`.  So `(W1) ∧ (W2)` does not imply `(W3)`, and the sentence's two
  clauses are two halves of the same fact.

`Sofic.CommutingLampCollapse` is the other half of the story: killing that
central sign makes the same lamp a genuine involutive witness.  The two modules
together say that the sign is the whole of the `(W3)` obstruction here.
-/

namespace GroupApproximation
namespace WreathWitnessW3

open MarkedCompression MappingTelescope CliffordLamp SemidirectProduct
open scoped commutatorElement

/-! ## Anticommuting coordinates do not commute -/

/-- **Anticommuting involutions do not commute.**  If `u` and `v` are
involutions of a ring with `1 + 1 ≠ 0` and `u v = -(v u)`, then `u` and `v` do
not commute, so no joint spectral calculus is available for them.  This is the
manuscript's "anticommuting Clifford coordinates have no joint spectral
labels", in the only form that does not presuppose a spectral theorem. -/
theorem not_commute_of_anticommute {A : Type*} [Ring A]
    (hchar : (1 : A) + 1 ≠ 0) {u v : A} (hu : u * u = 1) (hv : v * v = 1)
    (hanti : u * v = -(v * u)) : ¬ Commute u v := by
  intro hc
  have hvu : v * u = -(v * u) := hc.eq.symm.trans hanti
  have hsum : v * u + v * u = 0 := by
    nth_rewrite 1 [hvu]
    exact neg_add_cancel _
  have hprod : v * (v * u) * u = v * v * (u * u) := by
    rw [← mul_assoc v v u, mul_assoc (v * v) u u]
  have h0 : v * (v * u + v * u) * u = 0 := by
    rw [hsum, mul_zero, zero_mul]
  rw [mul_add, add_mul, hprod, hv, hu, mul_one] at h0
  exact hchar h0

/-! ## The concrete anticommuting pair, and how it breaks Step 2

The remark names the failure mode concretely: anticommuting Clifford
coordinates.  The smallest instance is the pair of `2 × 2` Pauli matrices, and
it refutes the Step 2 route outright rather than merely failing to supply it.

Step 2 of `thm:collapse` uses that for *commuting* exact involutions `u` and
`w` the difference `T = u - w` satisfies `T³ = 4T`; that identity is what turns
the Frobenius mass `Tr|u - w|²` into `4 · rank((u-w)²/4)`, and the joint
spectral calculus of the commuting pair is what supplies it.  For the
anticommuting pair the very same `T` satisfies `T³ = 2T`, so the rank identity
is off by a factor of two and Step 2 has no starting point.  That is the
concrete counterexample: not that the collapse conclusion fails, but that this
route to it does. -/

/-- The Pauli coordinate `X`. -/
def pauliX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The Pauli coordinate `Z`. -/
def pauliZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

theorem pauliX_mul_self : pauliX * pauliX = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pauliX, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

theorem pauliZ_mul_self : pauliZ * pauliZ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pauliZ, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

/-- **The two coordinates anticommute.** -/
theorem pauli_anticommute : pauliX * pauliZ = -(pauliZ * pauliX) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pauliX, pauliZ, Matrix.mul_apply, Fin.sum_univ_two]

theorem matrix_one_add_one_ne_zero :
    (1 : Matrix (Fin 2) (Fin 2) ℂ) + 1 ≠ 0 := by
  intro h
  have h00 : ((1 : Matrix (Fin 2) (Fin 2) ℂ) + 1) 0 0
      = (0 : Matrix (Fin 2) (Fin 2) ℂ) 0 0 := by rw [h]
  norm_num [Matrix.one_apply] at h00

/-- **The concrete anticommuting pair does not commute**, so it carries no
joint spectral labels.  This is `not_commute_of_anticommute` at the smallest
Clifford pair. -/
theorem not_commute_pauli : ¬ Commute pauliX pauliZ :=
  not_commute_of_anticommute matrix_one_add_one_ne_zero pauliX_mul_self
    pauliZ_mul_self pauli_anticommute

/-- **The sharp form of the failure.**  For the anticommuting pair the Step 2
difference squares to the scalar `2`, so `T²/4` is `1/2` and is *not* a
projection --- whereas for a commuting pair of involutions `T²/4` is exactly the
projection whose rank Step 2 counts. -/
theorem pauli_difference_sq :
    (pauliX - pauliZ) * (pauliX - pauliZ) =
      (2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pauliX, pauliZ, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply]

/-- For the anticommuting pair the Step 2 difference satisfies `T³ = 2T`. -/
theorem pauli_difference_cube :
    (pauliX - pauliZ) ^ 3 = (2 : ℂ) • (pauliX - pauliZ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pauliX, pauliZ, pow_succ, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.sub_apply, Matrix.smul_apply]

/-- **The Step 2 rank identity fails for the anticommuting pair.**  Two
self-adjoint involutions that anticommute instead of commuting give
`T³ = 2T`, not `T³ = 4T`, so the Frobenius-mass-equals-`4 · rank` step of the
collapse proof is simply false without `(W3)`. -/
theorem pauli_rank_identity_fails :
    (pauliX - pauliZ) ^ 3 ≠ (4 : ℂ) • (pauliX - pauliZ) := by
  intro h
  have h00 : ((pauliX - pauliZ) ^ 3) 0 0
      = ((4 : ℂ) • (pauliX - pauliZ)) 0 0 := by rw [h]
  norm_num [pauliX, pauliZ, pow_succ, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.sub_apply, Matrix.smul_apply] at h00

/-- **The concrete counterexample, in one statement.**  A pair of self-adjoint
involutions that anticommute, do not commute, and for which the Step 2 cube
identity reads `T³ = 2T` rather than `T³ = 4T`. -/
theorem pauli_witness_package :
    pauliX * pauliX = 1 ∧ pauliZ * pauliZ = 1 ∧
      pauliX * pauliZ = -(pauliZ * pauliX) ∧
      ¬ Commute pauliX pauliZ ∧
      (pauliX - pauliZ) ^ 3 = (2 : ℂ) • (pauliX - pauliZ) ∧
      (pauliX - pauliZ) ^ 3 ≠ (4 : ℂ) • (pauliX - pauliZ) :=
  ⟨pauliX_mul_self, pauliZ_mul_self, pauli_anticommute, not_commute_pauli,
    pauli_difference_cube, pauli_rank_identity_fails⟩

/-! ## The Clifford configuration fails `(W3)`

Throughout, `L` is the base copy of `Γ` inside the ambient group, `s` is the
stable letter, and `k = d = t c t⁻¹` is the moved root lamp. -/

universe u

variable {Γ : Type u} [Group Γ] (α : Γ →* Γ) (hα : Function.Injective α)

/-- The moved root lamp is the Clifford lamp at the witness site. -/
theorem movedRootLamp_eq :
    tAmbient α hα * cAmbient α hα * (tAmbient α hα)⁻¹ =
      inl (lamp (Cosets α hα) (tSite α hα)) :=
  conj_inl_lamp α hα (tVertical α hα) (rootCoset α hα)

/-- **(W1) holds.**  The moved root lamp is an involution. -/
theorem movedRootLamp_mul_self :
    (tAmbient α hα * cAmbient α hα * (tAmbient α hα)⁻¹) *
        (tAmbient α hα * cAmbient α hα * (tAmbient α hα)⁻¹) = 1 := by
  rw [movedRootLamp_eq α hα]
  have hl : lamp (Cosets α hα) (tSite α hα) *
      lamp (Cosets α hα) (tSite α hα) = 1 := by
    simpa [pow_two] using lamp_sq (Cosets α hα) (tSite α hα)
  rw [← map_mul, hl, map_one]

/-- The compressed copy of the base fixes the witness site, so it centralises
the moved root lamp. -/
theorem commute_compressed_movedRootLamp (γ₀ : Γ) :
    Commute (iotaAmbient α hα (α γ₀))
      (tAmbient α hα * cAmbient α hα * (tAmbient α hα)⁻¹) := by
  rw [movedRootLamp_eq α hα]
  have h1 := conj_inl_lamp α hα (iotaVertical α hα (α γ₀)) (tSite α hα)
  rw [iotaVertical_range_smul_tSite α hα γ₀] at h1
  exact mul_inv_eq_iff_eq_mul.mp h1

/-- **(W2) holds.**  The `t`-compressed copy of the base commutes with the
moved root lamp, because compression lands in `α(Γ)` and `α(Γ)` fixes the
witness site. -/
theorem commute_compressed_range_movedRootLamp (γ : Ambient α hα)
    (hγ : γ ∈ (iotaAmbient α hα).range) :
    Commute (tAmbient α hα * γ * (tAmbient α hα)⁻¹)
      (tAmbient α hα * cAmbient α hα * (tAmbient α hα)⁻¹) := by
  obtain ⟨γ₀, rfl⟩ := MonoidHom.mem_range.mp hγ
  rw [compress α hα γ₀]
  exact commute_compressed_movedRootLamp α hα γ₀

/-- **(W3) fails, and the obstruction is the central sign.**  The moved root
lamp and its conjugate by a mover do not commute: their commutator is the
marked word of `thm:A`, which is the nontrivial central Clifford sign.  This is
the manuscript's "anticommuting Clifford coordinates", at the group level. -/
theorem not_commute_conj_movedRootLamp {a₀ : Γ} (ha₀ : a₀ ∉ Set.range α) :
    ¬ Commute (tAmbient α hα * cAmbient α hα * (tAmbient α hα)⁻¹)
      (iotaAmbient α hα a₀ *
        (tAmbient α hα * cAmbient α hα * (tAmbient α hα)⁻¹) *
        (iotaAmbient α hα a₀)⁻¹) := by
  intro hc
  apply signAmbient_ne_one α hα
  rw [← marked_word_eq_sign α hα ha₀, markedCompressionWord]
  exact commutatorElement_eq_one_iff_commute.mpr hc

/-- **`(W1)` and `(W2)` do not imply `(W3)`.**  In the Kazhdan--Clifford
ambient group of a proper injective self-embedding, the moved root lamp
satisfies the involution condition and the centrality condition for the base
copy compressed by the stable letter, and yet it is not an involutive
compression witness: its conjugation orbit does not commute, the failing
commutator being exactly the central Clifford sign.

This is what "the commutation hypothesis `(W3)` is essential" asserts about the
hypothesis list.  It is *not* a counterexample to `thm:collapse`: the collapse
theorem quantifies over witnesses, and the manuscript's own sentence says the
anticommuting configuration collapses by the different mechanism of `thm:A`. -/
theorem cliffordCoordinates_fail_W3 {a₀ : Γ} (ha₀ : a₀ ∉ Set.range α) :
    (tAmbient α hα * cAmbient α hα * (tAmbient α hα)⁻¹) *
        (tAmbient α hα * cAmbient α hα * (tAmbient α hα)⁻¹) = 1 ∧
      (∀ γ ∈ (iotaAmbient α hα).range,
        Commute (tAmbient α hα * γ * (tAmbient α hα)⁻¹)
          (tAmbient α hα * cAmbient α hα * (tAmbient α hα)⁻¹)) ∧
      iotaAmbient α hα a₀ ∈ (iotaAmbient α hα).range ∧
      (1 : Ambient α hα) ∈ (iotaAmbient α hα).range ∧
      ¬ CollapseUniverseScope.IsInvolutiveCompressionWitness
          (iotaAmbient α hα).range (tAmbient α hα)
          (tAmbient α hα * cAmbient α hα * (tAmbient α hα)⁻¹) := by
  refine ⟨movedRootLamp_mul_self α hα,
    fun γ hγ => commute_compressed_range_movedRootLamp α hα γ hγ,
    MonoidHom.mem_range.mpr ⟨a₀, rfl⟩, Subgroup.one_mem _, ?_⟩
  intro hw
  refine not_commute_conj_movedRootLamp α hα ha₀ ?_
  have h := hw.2.2 1 (Subgroup.one_mem _) (iotaAmbient α hα a₀)
    (MonoidHom.mem_range.mpr ⟨a₀, rfl⟩)
  have hone : (1 : Ambient α hα) *
        (tAmbient α hα * cAmbient α hα * (tAmbient α hα)⁻¹) *
        (1 : Ambient α hα)⁻¹ =
      tAmbient α hα * cAmbient α hα * (tAmbient α hα)⁻¹ := by
    rw [one_mul, inv_one, mul_one]
  rw [hone] at h
  exact h

end WreathWitnessW3
end GroupApproximation
