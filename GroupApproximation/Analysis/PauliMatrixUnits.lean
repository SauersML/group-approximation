import GroupApproximation.Analysis.PauliStageOperators
import GroupApproximation.Analysis.MatrixUnitHom

/-!
# The finite Pauli stages of the hyperfinite II₁ factor

Infrastructure of lane `oa-hyperfinite` for "Brown's formulation" of `simple_kazhdan_sofic_group.tex`
(tex l.273–290 at 37551fd93).  The Pauli operators supported on the first `j` sites of `𝓡` span a
copy of `M_{2^j}(ℂ)`.  This module builds its matrix units and the unital, trace-preserving star
homomorphism `stageHom j : M_{2^j}(ℂ) → 𝓡`.

* `StageIdx j := Fin j → ZMod 2`, the matrix indices; `fdot`, their dot product.
* `sum_zsign_fdot`: character orthogonality `Σ_z s(z·c) = 2^j [c = 0]`, by the sign-reversing flip
  `z ↦ z + e_i` at a coordinate with `c_i = 1`.
* `stageEmb`: words of length `j` as sequences supported below `j`; `dot_stageEmb`.
* `stageOp x z`, the Pauli operators of stage `j`, with product and adjoint rules.
* `stageUnit a b := 2^{-j} Σ_z s(z·b) stageOp (a+b) z`, a system of matrix units
  (`stageUnit_mul`, `star_stageUnit`, `sum_stageUnit_diag`) with trace
  `τ(E_ab) = 2^{-j} [a = b]` (`coefficient_stageUnit`).
* `stageHom j`, `stageHom_mem`, `coefficient_stageHom`: `τ(stageHom j A) = 2^{-j} trace A`.
-/

namespace GroupApproximation
namespace Hyperfinite

open TwistedGroupVonNeumann ReducedGroupCStarTrace MatrixUnits

noncomputable section

/-! ## Binary words -/

/-- Binary words of length `j`: the matrix indices of the Pauli stage `j`. -/
abbrev StageIdx (j : ℕ) := Fin j → ZMod 2

variable {j : ℕ}

/-- The dot product of binary words. -/
def fdot (u v : StageIdx j) : ZMod 2 :=
  ∑ i, u i * v i

theorem fdot_add_left (u u' v : StageIdx j) : fdot (u + u') v = fdot u v + fdot u' v := by
  simp only [fdot, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem fdot_add_right (u v v' : StageIdx j) : fdot u (v + v') = fdot u v + fdot u v' := by
  simp only [fdot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

@[simp]
theorem fdot_zero_left (v : StageIdx j) : fdot 0 v = 0 := by
  simp [fdot]

@[simp]
theorem fdot_zero_right (u : StageIdx j) : fdot u 0 = 0 := by
  simp [fdot]

theorem fdot_comm (u v : StageIdx j) : fdot u v = fdot v u := by
  simp only [fdot, mul_comm]

theorem fdot_single_left (i : Fin j) (c : ZMod 2) (v : StageIdx j) :
    fdot (Pi.single i c) v = c * v i := by
  simp [fdot, Pi.single_apply, ite_mul]

theorem stageIdx_add_self (u : StageIdx j) : u + u = 0 := by
  funext i
  simp only [Pi.add_apply, Pi.zero_apply]
  exact CharTwo.add_self_eq_zero (u i)

theorem card_stageIdx : Fintype.card (StageIdx j) = 2 ^ j := by
  rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]

/-- **Character orthogonality** for binary words. -/
theorem sum_zsign_fdot (c : StageIdx j) :
    ∑ z : StageIdx j, zsign (fdot z c) = if c = 0 then (2 : ℂ) ^ j else 0 := by
  by_cases hc : c = 0
  · subst hc
    simp [Finset.card_univ, card_stageIdx]
  · rw [if_neg hc]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hc
    have hi1 : c i = 1 := zmod_two_eq_one_of_ne_zero hi
    have hflip := Equiv.sum_comp (Equiv.addRight (Pi.single i (1 : ZMod 2) : StageIdx j))
      (fun z : StageIdx j ↦ zsign (fdot z c))
    have hneg : ∑ z : StageIdx j, zsign (fdot (z + Pi.single i 1) c) =
        -∑ z : StageIdx j, zsign (fdot z c) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun z _ ↦ ?_
      rw [fdot_add_left, fdot_single_left, hi1, one_mul, zsign_add, zsign_one, mul_neg_one]
    have h : ∑ z : StageIdx j, zsign (fdot z c) = -∑ z : StageIdx j, zsign (fdot z c) := by
      rw [← hneg]
      exact hflip.symm
    linear_combination h / 2

/-! ## Words as sequences -/

/-- A binary word of length `j` as a finitely supported sequence. -/
def stageEmb (u : StageIdx j) : PauliCoord :=
  Finsupp.onFinset (Finset.range j) (fun i ↦ if h : i < j then u ⟨i, h⟩ else 0) (by
    intro i hi
    rw [Finset.mem_range]
    by_contra h
    exact hi (dif_neg h))

theorem stageEmb_apply (u : StageIdx j) (i : ℕ) :
    stageEmb u i = if h : i < j then u ⟨i, h⟩ else 0 :=
  Finsupp.onFinset_apply

theorem stageEmb_add (u v : StageIdx j) : stageEmb (u + v) = stageEmb u + stageEmb v := by
  ext i
  rw [Finsupp.add_apply, stageEmb_apply, stageEmb_apply, stageEmb_apply]
  split_ifs <;> simp

theorem stageEmb_zero : stageEmb (0 : StageIdx j) = 0 := by
  ext i
  rw [stageEmb_apply, Finsupp.zero_apply]
  split_ifs <;> rfl

theorem stageEmb_injective : Function.Injective (stageEmb (j := j)) := by
  intro u v h
  funext i
  have hi := congrArg (fun w : PauliCoord ↦ w i.val) h
  simpa [stageEmb_apply] using hi

theorem stageEmb_eq_zero_iff (u : StageIdx j) : stageEmb u = 0 ↔ u = 0 := by
  constructor
  · intro h
    exact stageEmb_injective (h.trans stageEmb_zero.symm)
  · intro h
    rw [h, stageEmb_zero]

theorem stageEmb_single (i : Fin j) (c : ZMod 2) :
    stageEmb (Pi.single i c) = Finsupp.single i.val c := by
  ext n
  rw [stageEmb_apply, Finsupp.single_apply]
  by_cases hn : n < j
  · rw [dif_pos hn, Pi.single_apply]
    by_cases h : (⟨n, hn⟩ : Fin j) = i
    · subst h
      simp
    · rw [if_neg h, if_neg]
      intro h'
      exact h (Fin.ext h'.symm)
  · rw [dif_neg hn, if_neg]
    intro h'
    exact hn (h' ▸ i.2)

/-- The dot product of embedded words is the dot product of the words. -/
theorem dot_stageEmb (u v : StageIdx j) : dot (stageEmb u) (stageEmb v) = fdot u v := by
  let L : StageIdx j →+ ZMod 2 :=
    { toFun := fun w ↦ dot (stageEmb w) (stageEmb v)
      map_zero' := by rw [stageEmb_zero, dot_zero_left]
      map_add' := fun w w' ↦ by rw [stageEmb_add, dot_add_left] }
  let R : StageIdx j →+ ZMod 2 :=
    { toFun := fun w ↦ fdot w v
      map_zero' := fdot_zero_left v
      map_add' := fun w w' ↦ fdot_add_left w w' v }
  have hLR : L = R := by
    refine AddMonoidHom.functions_ext _ L R fun i c ↦ ?_
    show dot (stageEmb (Pi.single i c)) (stageEmb v) = fdot (Pi.single i c) v
    rw [stageEmb_single, dot_single_left, fdot_single_left, stageEmb_apply, dif_pos i.2]
  exact DFunLike.congr_fun hLR u

/-! ## Stage operators -/

/-- The Pauli operator of a pair of binary words of length `j`. -/
def stageOp (x z : StageIdx j) : GroupHilbert PauliGroup →L[ℂ] GroupHilbert PauliGroup :=
  pauliOp (stageEmb x) (stageEmb z)

theorem stageOp_mem (x z : StageIdx j) : stageOp x z ∈ hyperfiniteFactor :=
  pauliOp_mem _ _

theorem stageOp_mul (x z x' z' : StageIdx j) :
    stageOp x z * stageOp x' z' = zsign (fdot z x') • stageOp (x + x') (z + z') := by
  rw [stageOp, stageOp, stageOp, pauliOp_mul, dot_stageEmb, stageEmb_add, stageEmb_add]

theorem star_stageOp (x z : StageIdx j) :
    star (stageOp x z) = zsign (fdot z x) • stageOp x z := by
  rw [stageOp, star_pauliOp, dot_stageEmb]

theorem stageOp_zero : stageOp (0 : StageIdx j) 0 = 1 := by
  rw [stageOp, stageEmb_zero, pauliOp_zero]

theorem coefficient_stageOp (x z : StageIdx j) :
    (stageOp x z (deltaOne PauliGroup)) 1 = if x = 0 ∧ z = 0 then 1 else 0 := by
  rw [stageOp, coefficient_pauliOp, stageEmb_eq_zero_iff, stageEmb_eq_zero_iff]

/-- The sum over a coordinate shift that the matrix-unit product reduces to. -/
theorem stageOp_mul_sum (x x' z d : StageIdx j) :
    ∑ z' : StageIdx j, zsign (fdot z' d) • (stageOp x z * stageOp x' z') =
      zsign (fdot z (d + x')) • ∑ w : StageIdx j, zsign (fdot w d) • stageOp (x + x') w := by
  rw [Finset.smul_sum, ← Equiv.sum_comp (Equiv.addRight z)]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  show zsign (fdot (w + z) d) • (stageOp x z * stageOp x' (w + z)) =
    zsign (fdot z (d + x')) • (zsign (fdot w d) • stageOp (x + x') w)
  rw [stageOp_mul, smul_smul, smul_smul, fdot_add_left, fdot_add_right, zsign_add, zsign_add]
  have hzw : z + (w + z) = w := by
    rw [add_comm w z, ← add_assoc, stageIdx_add_self, zero_add]
  rw [hzw]
  congr 1
  ring

/-! ## Matrix units -/

/-- **The matrix units of the Pauli stage `j`**: `E_ab = 2^{-j} Σ_z s(z·b) stageOp (a+b) z`. -/
def stageUnit (a b : StageIdx j) : GroupHilbert PauliGroup →L[ℂ] GroupHilbert PauliGroup :=
  ((2 : ℂ) ^ j)⁻¹ • ∑ z : StageIdx j, zsign (fdot z b) • stageOp (a + b) z

theorem stageUnit_mul (a b c d : StageIdx j) :
    stageUnit a b * stageUnit c d = if b = c then stageUnit a d else 0 := by
  have hexp : stageUnit a b * stageUnit c d =
      (((2 : ℂ) ^ j)⁻¹ * ((2 : ℂ) ^ j)⁻¹) •
        ((∑ z : StageIdx j, zsign (fdot z (b + c))) •
          ∑ w : StageIdx j, zsign (fdot w d) • stageOp (a + b + (c + d)) w) := by
    rw [stageUnit, stageUnit, smul_mul_smul_comm, Finset.sum_mul_sum, Finset.sum_smul]
    congr 1
    refine Finset.sum_congr rfl fun z _ ↦ ?_
    have hin : ∑ z' : StageIdx j,
        zsign (fdot z b) • stageOp (a + b) z * (zsign (fdot z' d) • stageOp (c + d) z') =
        zsign (fdot z b) •
          ∑ z' : StageIdx j, zsign (fdot z' d) • (stageOp (a + b) z * stageOp (c + d) z') := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun z' _ ↦ ?_
      rw [smul_mul_smul_comm, smul_smul]
    rw [hin, stageOp_mul_sum, smul_smul, ← zsign_add, ← fdot_add_right]
    have hidx : b + (d + (c + d)) = b + c := by
      rw [add_comm c d, ← add_assoc d d c, stageIdx_add_self, zero_add]
    rw [hidx]
  rw [hexp, sum_zsign_fdot]
  by_cases hbc : b = c
  · subst hbc
    rw [if_pos (stageIdx_add_self b), if_pos rfl, stageUnit, smul_smul]
    have hidx : a + b + (b + d) = a + d := by
      rw [add_assoc, ← add_assoc b b d, stageIdx_add_self, zero_add]
    rw [hidx]
    congr 1
    field_simp
  · have hbc' : b + c ≠ 0 := by
      intro h
      apply hbc
      have h' := congrArg (· + c) h
      simpa [add_assoc, stageIdx_add_self] using h'
    rw [if_neg hbc', if_neg hbc, zero_smul, smul_zero]

theorem star_stageUnit (a b : StageIdx j) : star (stageUnit a b) = stageUnit b a := by
  rw [stageUnit, stageUnit, star_smul, star_sum]
  have hscal : star (((2 : ℂ) ^ j)⁻¹) = ((2 : ℂ) ^ j)⁻¹ := by
    simp [star_inv₀, star_pow]
  rw [hscal]
  congr 1
  refine Finset.sum_congr rfl fun z _ ↦ ?_
  rw [star_smul, star_stageOp, smul_smul]
  have hs : star (zsign (fdot z b)) = zsign (fdot z b) := star_zsign _
  rw [hs, ← zsign_add, ← fdot_add_right, add_comm a b]
  have hidx : b + (b + a) = a := by
    rw [← add_assoc, stageIdx_add_self, zero_add]
  rw [hidx]

theorem sum_stageUnit_diag : ∑ a : StageIdx j, stageUnit a a = 1 := by
  simp only [stageUnit, stageIdx_add_self]
  rw [← Finset.smul_sum, Finset.sum_comm]
  have hin : ∀ z : StageIdx j,
      ∑ a : StageIdx j, zsign (fdot z a) • stageOp (0 : StageIdx j) z =
        if z = 0 then (2 : ℂ) ^ j • stageOp (0 : StageIdx j) z else 0 := by
    intro z
    rw [← Finset.sum_smul]
    have hs : ∑ a : StageIdx j, zsign (fdot z a) = if z = 0 then (2 : ℂ) ^ j else 0 := by
      rw [← sum_zsign_fdot z]
      exact Finset.sum_congr rfl fun a _ ↦ by rw [fdot_comm]
    rw [hs]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl fun z _ ↦ hin z]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [smul_smul, inv_mul_cancel₀ (pow_ne_zero j two_ne_zero), one_smul, stageOp_zero]

theorem coefficient_stageUnit (a b : StageIdx j) :
    ambientCoefficientAtOne PauliGroup (stageUnit a b) =
      if a = b then ((2 : ℂ) ^ j)⁻¹ else 0 := by
  rw [stageUnit, map_smul, map_sum]
  simp only [map_smul, ambientCoefficientAtOne_apply, coefficient_stageOp, smul_eq_mul]
  by_cases hab : a = b
  · subst hab
    simp [stageIdx_add_self, mul_ite, Finset.sum_ite_eq']
  · have hab' : a + b ≠ 0 := by
      intro h
      apply hab
      have h' := congrArg (· + b) h
      simpa [add_assoc, stageIdx_add_self] using h'
    simp [hab, hab']

theorem stageUnits_isMatrixUnits : IsMatrixUnits (stageUnit (j := j)) where
  mul := stageUnit_mul
  star := star_stageUnit

/-! ## The stage homomorphism -/

/-- **The Pauli stage `j`**: a unital star homomorphism `M_{2^j}(ℂ) → 𝓡`. -/
def stageHom (j : ℕ) :
    Matrix (StageIdx j) (StageIdx j) ℂ →⋆ₐ[ℂ]
      (GroupHilbert PauliGroup →L[ℂ] GroupHilbert PauliGroup) :=
  matrixUnitHom stageUnits_isMatrixUnits sum_stageUnit_diag

theorem stageUnit_mem (a b : StageIdx j) : stageUnit a b ∈ hyperfiniteFactor := by
  show ((2 : ℂ) ^ j)⁻¹ • ∑ z : StageIdx j, zsign (fdot z b) • stageOp (a + b) z ∈
    hyperfiniteFactor.toStarSubalgebra
  refine hyperfiniteFactor.toStarSubalgebra.smul_mem ?_ _
  refine sum_mem fun z _ ↦ ?_
  exact hyperfiniteFactor.toStarSubalgebra.smul_mem (stageOp_mem _ _) _

/-- **The stage lands in `𝓡`.** -/
theorem stageHom_mem (A : Matrix (StageIdx j) (StageIdx j) ℂ) :
    stageHom j A ∈ hyperfiniteFactor := by
  show ∑ a, ∑ b, A a b • stageUnit a b ∈ hyperfiniteFactor.toStarSubalgebra
  refine sum_mem fun a _ ↦ sum_mem fun b _ ↦ ?_
  exact hyperfiniteFactor.toStarSubalgebra.smul_mem (stageUnit_mem a b) _

/-- **The stage preserves the trace**: `τ(stageHom j A) = 2^{-j} trace A`. -/
theorem coefficient_stageHom (A : Matrix (StageIdx j) (StageIdx j) ℂ) :
    ambientCoefficientAtOne PauliGroup (stageHom j A) = ((2 : ℂ) ^ j)⁻¹ * Matrix.trace A :=
  trace_matrixUnitSum stageUnit (ambientCoefficientAtOne PauliGroup).toLinearMap
    ((2 : ℂ) ^ j)⁻¹ coefficient_stageUnit A

end

#audit_axioms sum_zsign_fdot
#audit_axioms stageUnit_mul
#audit_axioms sum_stageUnit_diag
#audit_axioms coefficient_stageHom

end Hyperfinite
end GroupApproximation
