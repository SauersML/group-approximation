import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ObstructionExtClass
import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ObstructionSplitExtBusby

/-!
# The Busby map of a C⋆-extension

Lane `TWWSch3d4a-B`, work order `TWWSch3d4a-ABC` (C). Sources: G. Elliott and D. Kucerovsky,
*An abstract Voiculescu–Brown–Douglas–Fillmore absorption theorem*, Pacific J. Math. 198 (2001),
§2; C. Schafhauser, *A new proof of the Tikuisis–White–Winter theorem*, J. reine angew. Math. 759
(2020), §§4–5; manuscript `non_mf_group_notes.tex`, `thm:fixed-radical-membership`
(l. 1376–1378).

An extension `X : CStarExtension S J` has the Busby cycle `X.busbyCycle` (`ObstructionExtClass`),
whose lifts are the corner operators `cornerOp e = V ∘ multOp e ∘ V⋆` on `H_J = ℓ²(ℕ, J)`. Composing
with the corona quotient gives the **Busby map** of `X`

`X.busbyₙ : S →⋆ₙₐ[ℂ] StdCorona J`, `X.busbyₙ (X.quot e) = [cornerOp e]`.

## Correction: the Busby map into `Q(J ⊗ 𝒦)` is not unital

The work order asks for a *unital* `CStarExtension.busby : S →⋆ₐ[ℂ] StdCorona J`. As written this is
false: the corner construction sends `1` to the corner projection `[V V⋆]` (`busbyₙ_one`), and
`V V⋆` is the identity modulo compacts only when `J` has a left unit
(`exists_leftUnit_of_busbyₙ_one`, `exists_leftUnit_of_isUnital`). Compressing
`cornerOp e - 1` by the isometry `W : b ↦ (0, b, 0, …)` gives `-1` on `J`, which is compact iff `J`
has a left unit (`IsCompactOp.exists_ofElem`). For the stable ideals of Schafhauser §5 (and
`J = K`) there is none, so `not_isUnital_busbyCycleOfLift` shows the unital Busby map cannot exist.
In EK 2001 §2 the Busby map lands in the corona `M(J)/J`, with image in the corner
`[V V⋆] Q(J ⊗ 𝒦) [V V⋆]`, where it is unital. We record the non-unital map together with the
value `[V V⋆]` at `1`.

* `coordAt J n` (`b ↦ b` in coordinate `n`) and `isBoundedBy_coordAt`; `stdCornerProj J = [V V⋆]`;
* `CStarExtension.busbyₙ`, `busbyₙ_apply`, `busbyₙ_quot`, `busbyₙ_eq_busbyCycleOfLift`;
* `busbyₙ_one : X.busbyₙ 1 = stdCornerProj J`;
* `exists_leftUnit_of_compactEq_cornerOp_id`, `exists_leftUnit_of_isUnital`,
  `exists_leftUnit_of_busbyₙ_one`, `not_isUnital_busbyCycleOfLift`: the necessity of the correction.
-/

noncomputable section

namespace GroupApproximation.Full.TWWSchafhauser

open GroupApproximation.HilbertModule

section CoordVecAt

variable {J : Type} [NonUnitalCStarAlgebra J]

/-- The sequence with `b` in coordinate `n` and `0` elsewhere. -/
def coordVecAt (n : ℕ) (b : J) : ℕ → J := fun i => if i = n then b else 0

theorem coordVecAt_self (n : ℕ) (b : J) : coordVecAt n b n = b := if_pos rfl

theorem coordVecAt_of_ne (b : J) {n i : ℕ} (h : i ≠ n) : coordVecAt n b i = 0 := if_neg h

theorem summable_coordVecAt (n : ℕ) (b : J) :
    Summable fun i => star (coordVecAt n b i) * coordVecAt n b i :=
  summable_of_ne_finset_zero (s := {n}) fun i hi => by
    show star (coordVecAt n b i) * coordVecAt n b i = 0
    rw [coordVecAt_of_ne b (Finset.notMem_singleton.mp hi), star_zero, zero_mul]

end CoordVecAt

section CoordAt

variable {J : Type} [NonUnitalCStarAlgebra J] [PartialOrder J] [StarOrderedRing J]

variable (J) in
/-- The isometry `J → H_J` onto coordinate `n`. Its adjoint reads off coordinate `n`. -/
def coordAt (n : ℕ) : Adjointable (selfModule J) (standardModule ℕ J) where
  toFun b := ⟨coordVecAt n b, summable_coordVecAt n b⟩
  adj f := f.1 n
  inner_adj b f := by
    show (∑' i, star (coordVecAt n b i) * f.1 i) = star b * f.1 n
    rw [tsum_eq_single n, coordVecAt_self]
    intro i hi
    rw [coordVecAt_of_ne b hi, star_zero, zero_mul]

theorem coordAt_adj_toFun (n : ℕ) (b : J) : (coordAt J n).adj ((coordAt J n).toFun b) = b :=
  coordVecAt_self n b

variable (J) in
/-- `coordAt J n` is an isometry, and in particular bounded by `1`. -/
theorem isBoundedBy_coordAt (n : ℕ) : (coordAt J n).IsBoundedBy 1 := by
  intro b
  have h : (standardModule ℕ J).inner ((coordAt J n).toFun b) ((coordAt J n).toFun b) =
      star b * b :=
    ((coordAt J n).inner_adj b _).trans (congrArg (star b * ·) (coordAt_adj_toFun n b))
  exact le_of_eq ((congrArg (fun z : J => Real.sqrt ‖z‖) h).trans (one_mul _).symm)

variable (J) in
/-- The corner projection `[V V⋆] ∈ Q(J ⊗ 𝒦)`, `V = coordZero J`. -/
def stdCornerProj : StdCorona J :=
  stdCoronaMk (Adjointable.comp (coordZero J) (Adjointable.adjoint (coordZero J)))

variable (J) in
theorem isBounded_coordZero_comp_adjoint :
    (Adjointable.comp (coordZero J) (Adjointable.adjoint (coordZero J))).IsBounded :=
  ((isBoundedBy_coordZero J).comp ((isBoundedBy_coordZero J).adjoint zero_le_one)
    zero_le_one).isBounded (mul_nonneg zero_le_one zero_le_one)

end CoordAt

namespace CStarExtension

section Unit

variable {S : Type} [CStarAlgebra S] {J : Type} [NonUnitalCStarAlgebra J]
variable (X : CStarExtension S J)

theorem leftMul_one (j : J) : X.leftMul 1 j = j :=
  X.leftMul_eq_iff.mpr (one_mul (X.incl j))

end Unit

section Busby

variable {S : Type} [CStarAlgebra S]
variable {J : Type} [NonUnitalCStarAlgebra J] [PartialOrder J] [StarOrderedRing J]
variable (X : CStarExtension S J)

/-- **The Busby map** `S → Q(J ⊗ 𝒦)` of the extension `X`, a non-unital `⋆`-homomorphism. -/
def busbyₙ : S →⋆ₙₐ[ℂ] StdCorona J :=
  X.busbyCycle.busbyₙ

theorem busbyₙ_apply (a : S) :
    X.busbyₙ a = stdCoronaMk (X.cornerOp (Function.surjInv X.quot_surjective a)) :=
  X.busbyCycle.busbyₙ_apply a

/-- The Busby map does not depend on the lift. -/
theorem busbyₙ_eq_busbyCycleOfLift (σ : X.Lift) : X.busbyₙ = (X.busbyCycleOfLift σ).busbyₙ :=
  (BusbyCycle.busbyₙ_eq_iff X.busbyCycle (X.busbyCycleOfLift σ)).mpr fun a =>
    X.compactEq_cornerOp (Function.surjInv X.quot_surjective a) (σ.1 a) (fun _ => rfl)
      (fun _ => rfl) ((Function.surjInv_eq X.quot_surjective a).trans (σ.2 a).symm)

/-- `X.busbyₙ (X.quot e) = [cornerOp e]`. -/
theorem busbyₙ_quot (e : X.E) : X.busbyₙ (X.quot e) = stdCoronaMk (X.cornerOp e) :=
  (X.busbyₙ_apply (X.quot e)).trans
    ((stdCoronaMk_eq_iff
      ((X.isBoundedBy_cornerOp (Function.surjInv X.quot_surjective (X.quot e))).isBounded
        (norm_nonneg _))
      ((X.isBoundedBy_cornerOp e).isBounded (norm_nonneg e))).mpr
      (X.compactEq_cornerOp (Function.surjInv X.quot_surjective (X.quot e)) e (fun _ => rfl)
        (fun _ => rfl) (Function.surjInv_eq X.quot_surjective (X.quot e))))

/-- **The Busby map sends `1` to the corner projection** `[V V⋆]`. -/
theorem busbyₙ_one : X.busbyₙ 1 = stdCornerProj J :=
  (X.busbyₙ_apply 1).trans
    ((stdCoronaMk_eq_iff
      ((X.isBoundedBy_cornerOp (Function.surjInv X.quot_surjective 1)).isBounded
        (norm_nonneg _))
      (isBounded_coordZero_comp_adjoint J)).mpr
      (X.compactEq_cornerOp (Function.surjInv X.quot_surjective 1) 1 (fun _ => rfl)
        (fun f => congrArg (coordZero J).toFun (X.leftMul_one ((coordZero J).adj f)).symm)
        ((Function.surjInv_eq X.quot_surjective 1).trans (map_one X.quot).symm)))

/-- **Necessity of the correction.** If a corner operator is the identity modulo compacts, then
`J` has a left unit: compressing `cornerOp e - 1` by `W = coordAt J 1` gives `-1` on `J`. -/
theorem exists_leftUnit_of_compactEq_cornerOp_id (e : X.E)
    (h : CompactEq J (X.cornerOp e) (Adjointable.id (standardModule ℕ J))) :
    ∃ u : J, ∀ x : J, u * x = x := by
  have h' : Adjointable.IsCompactOp
      (Adjointable.sub (X.cornerOp e) (Adjointable.id (standardModule ℕ J))) := h
  have hW : (coordAt J 1).IsBounded := (isBoundedBy_coordAt J 1).isBounded zero_le_one
  have hKc := (h'.comp_right hW).comp_left hW.adjoint
  obtain ⟨c, hc⟩ := hKc.exists_ofElem
  refine ⟨-c, fun x => ?_⟩
  have hx : (-x : J) = c * x := by
    rw [← hc x]
    show -x = coordVec (X.leftMul e ((coordZero J).adj ((coordAt J 1).toFun x))) 1 -
      coordVecAt 1 x 1
    rw [coordVec_of_ne _ one_ne_zero, coordVecAt_self, zero_sub]
  rw [neg_mul, ← hx, neg_neg]

/-- A unital Busby cycle of corner operators forces a left unit in `J`. -/
theorem exists_leftUnit_of_isUnital (σ : X.Lift) (h : (X.busbyCycleOfLift σ).IsUnital) :
    ∃ u : J, ∀ x : J, u * x = x :=
  X.exists_leftUnit_of_compactEq_cornerOp_id (σ.1 1) h

/-- A unital Busby map forces a left unit in `J`. -/
theorem exists_leftUnit_of_busbyₙ_one (h : X.busbyₙ 1 = 1) : ∃ u : J, ∀ x : J, u * x = x :=
  X.exists_leftUnit_of_compactEq_cornerOp_id (Function.surjInv X.quot_surjective 1)
    ((stdCoronaQuot_eq_iff (X.busbyCycle.bddLift 1) 1).mp
      (h.trans (map_one (stdCoronaQuot J)).symm))

/-- Without a left unit in `J` (e.g. `J` stable), no Busby cycle of corner operators is unital:
the unital `CStarExtension.busby` of the work order does not exist. -/
theorem not_isUnital_busbyCycleOfLift (hJ : ∀ u : J, ∃ x : J, u * x ≠ x) (σ : X.Lift) :
    ¬ (X.busbyCycleOfLift σ).IsUnital := fun h => by
  obtain ⟨u, hu⟩ := X.exists_leftUnit_of_isUnital σ h
  obtain ⟨x, hx⟩ := hJ u
  exact hx (hu x)

/-- Without a left unit in `J`, the Busby map is not unital. -/
theorem busbyₙ_one_ne_one (hJ : ∀ u : J, ∃ x : J, u * x ≠ x) : X.busbyₙ 1 ≠ 1 := fun h => by
  obtain ⟨u, hu⟩ := X.exists_leftUnit_of_busbyₙ_one h
  obtain ⟨x, hx⟩ := hJ u
  exact hx (hu x)

end Busby

end CStarExtension

end GroupApproximation.Full.TWWSchafhauser

end
