import GroupApproximation.Analysis.PauliMatrixUnits
import GroupApproximation.Meta.AxiomGuard

/-!
# Brown's formulation: shifted Pauli words commute with a Pauli stage

`simple_kazhdan_sofic_group.tex`, subsection "Brown's formulation":

> Then $G$ lies in the unitary group of the McDuff factor $L(G)\mathbin{\bar\otimes}\mathcal R$,
> which embeds in $\mathcal R^\omega\mathbin{\bar\otimes}\mathcal R\subseteq
> (\mathcal R\mathbin{\bar\otimes}\mathcal R)^\omega\cong\mathcal R^\omega$.

This is the eighth step of this lane's route. The isomorphism `𝓡 ⊗̄ 𝓡 ≅ 𝓡`, used coordinatewise,
moves the second tensor factor past the sites that the first one uses. A Pauli word `p = (x, z)`
of `𝓡` shifted by `j` sites is `shiftOp j p := pauliOp (x ∘ (· - j)) (z ∘ (· - j))`. This file
proves:

* `shiftOp_mul`, `star_shiftOp`, `shiftOp_one`: the shifted words obey the Pauli relations
  `λ_p λ_q = s(σ(p,q)) λ_{pq}`, since the shift preserves the dot product (`dot_shiftCoord`).
* `commute_shiftOp_stageHom`: they commute with the stage `stageHom j : M_{2^j}(ℂ) → 𝓡`, because
  the shifted supports and the stage supports are disjoint.
* `coefficient_shiftOp_mul_stageHom`: `τ(shiftOp j p · stageHom j B) = 0` for `p ≠ 1`, because
  every product `shiftOp j p · stageOp x z` is a Pauli word with a nonzero shifted part.
* `norm_shiftOp_le`: `‖shiftOp j p‖ ≤ 1`.
-/

namespace GroupApproximation.Full.SK06

open Hyperfinite TwistedGroupVonNeumann ReducedGroupCStarTrace

noncomputable section

/-! ## Shifted coordinates -/

/-- Shift a finitely supported sequence `j` sites to the right. -/
def shiftCoord (j : ℕ) : PauliCoord →+ PauliCoord :=
  Finsupp.mapDomain.addMonoidHom (· + j)

theorem shiftCoord_apply' (j : ℕ) (v : PauliCoord) :
    shiftCoord j v = Finsupp.mapDomain (· + j) v :=
  rfl

/-- The shifted sequence at `i + j` is the original one at `i`. -/
theorem shiftCoord_apply_add (j : ℕ) (v : PauliCoord) (i : ℕ) :
    shiftCoord j v (i + j) = v i :=
  Finsupp.mapDomain_apply (add_left_injective j) v i

/-- The shifted sequence vanishes on the first `j` sites. -/
theorem shiftCoord_apply_lt (j : ℕ) (v : PauliCoord) {i : ℕ} (hi : i < j) :
    shiftCoord j v i = 0 := by
  rw [shiftCoord_apply']
  refine Finsupp.mapDomain_notin_range v i ?_
  rintro ⟨k, hk⟩
  have hk' : k + j = i := hk
  omega

/-- The shift preserves the dot product. -/
theorem dot_shiftCoord (j : ℕ) (u v : PauliCoord) :
    dot (shiftCoord j u) (shiftCoord j v) = dot u v := by
  show (shiftCoord j u).sum (fun i c ↦ c * shiftCoord j v i) = u.sum fun i c ↦ c * v i
  rw [shiftCoord_apply' j u, Finsupp.sum_mapDomain_index (h := fun i c ↦ c * shiftCoord j v i)
    (fun _ ↦ zero_mul _) (fun _ _ _ ↦ add_mul _ _ _)]
  exact Finsupp.sum_congr fun i _ ↦ by
    show u i * shiftCoord j v (i + j) = u i * v i
    rw [shiftCoord_apply_add]

variable {j : ℕ}

theorem lt_of_stageEmb_ne_zero {x : StageIdx j} {i : ℕ} (h : stageEmb x i ≠ 0) : i < j := by
  by_contra hij
  rw [stageEmb_apply, dif_neg hij] at h
  exact h rfl

/-- Stage words and shifted words have disjoint supports. -/
theorem dot_stageEmb_shiftCoord (x : StageIdx j) (v : PauliCoord) :
    dot (stageEmb x) (shiftCoord j v) = 0 := by
  show ∑ i ∈ (stageEmb x).support, stageEmb x i * shiftCoord j v i = 0
  refine Finset.sum_eq_zero fun i hi ↦ ?_
  rw [shiftCoord_apply_lt j v (lt_of_stageEmb_ne_zero (Finsupp.mem_support_iff.mp hi)),
    mul_zero]

/-- Shifted words and stage words have disjoint supports. -/
theorem dot_shiftCoord_stageEmb (v : PauliCoord) (x : StageIdx j) :
    dot (shiftCoord j v) (stageEmb x) = 0 := by
  show ∑ i ∈ (shiftCoord j v).support, shiftCoord j v i * stageEmb x i = 0
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  by_cases hij : i < j
  · rw [shiftCoord_apply_lt j v hij, zero_mul]
  · rw [stageEmb_apply, dif_neg hij, mul_zero]

/-- A shifted sequence plus a stage sequence vanishes only if the shifted part does. -/
theorem eq_zero_of_shiftCoord_add_stageEmb {v : PauliCoord} {x : StageIdx j}
    (h : shiftCoord j v + stageEmb x = 0) : v = 0 := by
  ext i
  have hi := DFunLike.congr_fun h (i + j)
  have hij : ¬(i + j < j) := by omega
  rw [Finsupp.add_apply, shiftCoord_apply_add, stageEmb_apply, dif_neg hij, add_zero,
    Finsupp.zero_apply] at hi
  rw [Finsupp.zero_apply]
  exact hi

/-- In characteristic two every Pauli group element is its own inverse. -/
theorem pauliGroup_inv_self (p : PauliGroup) : p⁻¹ = p := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_inv]
  exact Prod.ext (pauliCoord_neg _) (pauliCoord_neg _)

/-! ## Shifted Pauli operators -/

/-- The Pauli word `p` shifted `j` sites to the right. -/
def shiftOp (j : ℕ) (p : PauliGroup) : GroupHilbert PauliGroup →L[ℂ] GroupHilbert PauliGroup :=
  pauliOp (shiftCoord j (Multiplicative.toAdd p).1) (shiftCoord j (Multiplicative.toAdd p).2)

/-- Shifted words lie in `𝓡`. -/
theorem shiftOp_mem (j : ℕ) (p : PauliGroup) : shiftOp j p ∈ hyperfiniteFactor :=
  pauliOp_mem _ _

/-- The shifted word of `1` is the identity. -/
theorem shiftOp_one (j : ℕ) : shiftOp j 1 = 1 := by
  show pauliOp (shiftCoord j 0) (shiftCoord j 0) = 1
  rw [map_zero, pauliOp_zero]

/-- Shifted words multiply like the Pauli words they shift. -/
theorem shiftOp_mul (j : ℕ) (p q : PauliGroup) :
    shiftOp j p * shiftOp j q = zsign (pauliCocycle p q) • shiftOp j (p * q) := by
  have h1 : shiftCoord j (Multiplicative.toAdd (p * q)).1 =
      shiftCoord j (Multiplicative.toAdd p).1 + shiftCoord j (Multiplicative.toAdd q).1 :=
    map_add (shiftCoord j) (Multiplicative.toAdd p).1 (Multiplicative.toAdd q).1
  have h2 : shiftCoord j (Multiplicative.toAdd (p * q)).2 =
      shiftCoord j (Multiplicative.toAdd p).2 + shiftCoord j (Multiplicative.toAdd q).2 :=
    map_add (shiftCoord j) (Multiplicative.toAdd p).2 (Multiplicative.toAdd q).2
  have h0 : pauliCocycle p q = dot (Multiplicative.toAdd p).2 (Multiplicative.toAdd q).1 := rfl
  rw [h0, shiftOp, shiftOp, shiftOp, pauliOp_mul, dot_shiftCoord, h1, h2]

/-- Adjoints of shifted words are signed shifted words. -/
theorem star_shiftOp (j : ℕ) (p : PauliGroup) :
    star (shiftOp j p) = zsign (pauliCocycle p p⁻¹) • shiftOp j p⁻¹ := by
  have h0 : pauliCocycle p p = dot (Multiplicative.toAdd p).2 (Multiplicative.toAdd p).1 := rfl
  rw [pauliGroup_inv_self p, h0, shiftOp, star_pauliOp, dot_shiftCoord]

/-- Shifted words are contractions. -/
theorem norm_shiftOp_le (j : ℕ) (p : PauliGroup) : ‖shiftOp j p‖ ≤ 1 := by
  rw [shiftOp, pauliOp, twistedLeftOperator]
  exact LinearIsometry.norm_toContinuousLinearMap_le _

/-! ## Commutation with the stage -/

/-- Shifted words commute with the stage words. -/
theorem commute_shiftOp_stageOp (p : PauliGroup) (x z : StageIdx j) :
    Commute (shiftOp j p) (stageOp x z) := by
  show shiftOp j p * stageOp x z = stageOp x z * shiftOp j p
  rw [shiftOp, stageOp, pauliOp_mul, pauliOp_mul, dot_shiftCoord_stageEmb,
    dot_stageEmb_shiftCoord, zsign_zero, one_smul, one_smul,
    add_comm (shiftCoord j (Multiplicative.toAdd p).1),
    add_comm (shiftCoord j (Multiplicative.toAdd p).2)]

/-- Shifted words commute with the stage matrix units. -/
theorem commute_shiftOp_stageUnit (p : PauliGroup) (a b : StageIdx j) :
    Commute (shiftOp j p) (stageUnit a b) := by
  rw [stageUnit]
  refine Commute.smul_right ?_ _
  exact Commute.sum_right _ _ _ fun z _ ↦ (commute_shiftOp_stageOp p (a + b) z).smul_right _

/-- **Shifted words commute with the stage `j`.** -/
theorem commute_shiftOp_stageHom (p : PauliGroup) (B : Matrix (StageIdx j) (StageIdx j) ℂ) :
    Commute (shiftOp j p) (stageHom j B) := by
  have e : stageHom j B = ∑ a, ∑ b, B a b • stageUnit a b := rfl
  rw [e]
  exact Commute.sum_right _ _ _ fun a _ ↦ Commute.sum_right _ _ _ fun b _ ↦
    (commute_shiftOp_stageUnit p a b).smul_right _

/-! ## Traces -/

/-- A nontrivial shifted word times a stage word has trace `0`. -/
theorem coefficient_shiftOp_mul_stageOp {p : PauliGroup} (hp : p ≠ 1) (x z : StageIdx j) :
    ambientCoefficientAtOne PauliGroup (shiftOp j p * stageOp x z) = 0 := by
  have hne : ¬(shiftCoord j (Multiplicative.toAdd p).1 + stageEmb x = 0 ∧
      shiftCoord j (Multiplicative.toAdd p).2 + stageEmb z = 0) := by
    rintro ⟨h1, h2⟩
    exact hp (Multiplicative.toAdd.injective
      (Prod.ext (eq_zero_of_shiftCoord_add_stageEmb h1)
        (eq_zero_of_shiftCoord_add_stageEmb h2)))
  rw [shiftOp, stageOp, pauliOp_mul, map_smul, ambientCoefficientAtOne_apply,
    coefficient_pauliOp, if_neg hne, smul_zero]

/-- **The trace of a nontrivial shifted word times a stage element vanishes.** -/
theorem coefficient_shiftOp_mul_stageHom {p : PauliGroup} (hp : p ≠ 1)
    (B : Matrix (StageIdx j) (StageIdx j) ℂ) :
    ambientCoefficientAtOne PauliGroup (shiftOp j p * stageHom j B) = 0 := by
  have e : stageHom j B = ∑ a, ∑ b, B a b • stageUnit a b := rfl
  rw [e, Finset.mul_sum, map_sum]
  refine Finset.sum_eq_zero fun a _ ↦ ?_
  rw [Finset.mul_sum, map_sum]
  refine Finset.sum_eq_zero fun b _ ↦ ?_
  have hz : ∑ z : StageIdx j, ambientCoefficientAtOne PauliGroup
      (shiftOp j p * (zsign (fdot z b) • stageOp (a + b) z)) = 0 := by
    refine Finset.sum_eq_zero fun z _ ↦ ?_
    rw [mul_smul_comm, map_smul, coefficient_shiftOp_mul_stageOp hp, smul_zero]
  rw [mul_smul_comm, map_smul, stageUnit, mul_smul_comm, map_smul, Finset.mul_sum, map_sum, hz,
    smul_zero, smul_zero]

end

end GroupApproximation.Full.SK06

#audit_axioms GroupApproximation.Full.SK06.commute_shiftOp_stageHom
#audit_axioms GroupApproximation.Full.SK06.coefficient_shiftOp_mul_stageHom
#audit_axioms GroupApproximation.Full.SK06.shiftOp_mul
