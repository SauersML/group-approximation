import GroupApproximation.BooneHigmanLinear.CharZero.BTri.StepGen
import GroupApproximation.BooneHigmanLinear.CharZero.BTri.Develop
import GroupApproximation.BooneHigman.Metabelian.AbsorptionEndpoint
import GroupApproximation.Meta.AxiomGuard

/-!
# The local homomorphisms on the vertex stabilizers (Z1-base, piece Z.6, part 2)

Let `G = SL₃(B)`, `B = A[1/p]`, act on the building. Let `N ⊴ St₃(B)` contain `δᵢ(ι(K₂(3, A)))`
for the three twists `δᵢ` (`BTri/StepGen.lean`). Then each vertex stabilizer `Pᵢ = Stab(sᵢ)`
has a homomorphism `localHom N i : Pᵢ →* St₃(B)/N`:

  `Pᵢ --conj by Dᵢ--> P₀ --entries in A--> SL₃(A) = E₃(A) ≅ St₃(A)/K₂ --δᵢ ∘ ι--> St₃(B)/N`.

The inputs are:
* `hstab0`, the stabilizer of `s₀` is `SL₃(A)` (lane fix-bh-a, `stabilizer_std_zero`);
* `hSL`, `SL₃(A) = E₃(A)`;
* `hinj`, `ι : A → B` is injective.

`localHom_twist` computes it on the elements that come from `δᵢ(ι(St₃(A)))`. `liftI i` is a lift
to `St₃(B)` that does not depend on `N` (`localHom_eq_mk_liftI`).
-/

namespace GroupApproximation
namespace BooneHigmanLinear
namespace BTri

open GroupApproximation.SteinbergGroup
open GroupApproximation.BooneHigman.SteinbergBasic
open GroupApproximation.BooneHigman.Metabelian

/-- `SL₃(R)`. -/
abbrev SL3 (R : Type*) [CommRing R] : Type _ :=
  Matrix.SpecialLinearGroup (Fin 3) R

section Conj

variable {R : Type*} [CommRing R]

/-- Conjugation `γ ↦ D⁻¹ γ D` of `SL₃(R)` by `D ∈ GL₃(R)`. -/
def slConj (D : Matrix.GeneralLinearGroup (Fin 3) R) : SL3 R →* SL3 R where
  toFun γ := ⟨((D⁻¹ : Matrix.GeneralLinearGroup (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) *
      (γ : Matrix (Fin 3) (Fin 3) R) * (D : Matrix (Fin 3) (Fin 3) R), by
    rw [Matrix.det_mul, Matrix.det_mul, γ.2, mul_one, ← Matrix.det_mul, Units.inv_mul,
      Matrix.det_one]⟩
  map_one' := Subtype.ext (by
    change ((D⁻¹ : Matrix.GeneralLinearGroup (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * 1 *
      (D : Matrix (Fin 3) (Fin 3) R) = 1
    rw [Matrix.mul_one, Units.inv_mul])
  map_mul' γ δ := Subtype.ext (by
    change ((D⁻¹ : Matrix.GeneralLinearGroup (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) *
        ((γ : Matrix (Fin 3) (Fin 3) R) * (δ : Matrix (Fin 3) (Fin 3) R)) *
        (D : Matrix (Fin 3) (Fin 3) R) =
      ((D⁻¹ : Matrix.GeneralLinearGroup (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) *
          (γ : Matrix (Fin 3) (Fin 3) R) * (D : Matrix (Fin 3) (Fin 3) R) *
        (((D⁻¹ : Matrix.GeneralLinearGroup (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) *
          (δ : Matrix (Fin 3) (Fin 3) R) * (D : Matrix (Fin 3) (Fin 3) R))
    simp only [Matrix.mul_assoc, Units.mul_inv_cancel_left])

theorem toGL_slConj (D : Matrix.GeneralLinearGroup (Fin 3) R) (γ : SL3 R) :
    Matrix.SpecialLinearGroup.toGL (slConj D γ) = D⁻¹ * Matrix.SpecialLinearGroup.toGL γ * D :=
  Units.ext rfl

#audit_axioms toGL_slConj

/-- An elementary matrix has determinant `1`. -/
theorem det_of_mem_elementaryGroup {u : (Matrix (Fin 3) (Fin 3) R)ˣ}
    (hu : u ∈ elementaryGroup (Fin 3) R) : Matrix.det (u : Matrix (Fin 3) (Fin 3) R) = 1 := by
  induction hu using Subgroup.closure_induction with
  | mem u hu =>
      obtain ⟨i, j, hij, a, rfl⟩ := hu
      exact Matrix.det_transvection_of_ne i j hij a
  | one => simp
  | mul u v _ _ hu hv => rw [Units.val_mul, Matrix.det_mul, hu, hv, mul_one]
  | inv u _ hu =>
      have h := congrArg Matrix.det (Units.inv_mul u)
      rw [Matrix.det_mul, hu, mul_one, Matrix.det_one] at h
      exact h

#audit_axioms det_of_mem_elementaryGroup

/-- `E₃(R) →* SL₃(R)`. -/
def elemToSL : elementaryGroup (Fin 3) R →* SL3 R where
  toFun e := ⟨((e : (Matrix (Fin 3) (Fin 3) R)ˣ) : Matrix (Fin 3) (Fin 3) R),
    det_of_mem_elementaryGroup e.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem toGL_elemToSL (e : elementaryGroup (Fin 3) R) :
    Matrix.SpecialLinearGroup.toGL (elemToSL e) = (e : (Matrix (Fin 3) (Fin 3) R)ˣ) :=
  Units.ext rfl

#audit_axioms toGL_elemToSL

end Conj

section Stab

variable {A : Type*} [CommRing A] {p : A}

/-- The vertex stabilizers of `SL₃(A[1/p])`. -/
noncomputable abbrev vstab (i : Fin 3) : Subgroup (SL3 (Localization.Away p)) :=
  stabs (SL3 (Localization.Away p)) (stdVertex A p) i

theorem stdVertex_eq_smul (i : Fin 3) :
    stdVertex A p i = stdMat A p i • stdVertex A p 0 := by
  rw [stdVertex, stdVertex, smul_vertexOf]
  congr 1
  exact (mul_one _).symm

#audit_axioms stdVertex_eq_smul

/-- `γ` fixes `sᵢ` iff its conjugate by `Dᵢ` fixes `s₀`. -/
theorem mem_vstab_iff (i : Fin 3) (γ : SL3 (Localization.Away p)) :
    γ ∈ vstab (A := A) (p := p) i ↔ slConj (stdMat A p i) γ ∈ vstab (A := A) (p := p) 0 := by
  change γ • stdVertex A p i = stdVertex A p i ↔
    slConj (stdMat A p i) γ • stdVertex A p 0 = stdVertex A p 0
  rw [sl_smul_def, sl_smul_def, toGL_slConj, mul_smul, mul_smul, ← stdVertex_eq_smul,
    inv_smul_eq_iff, ← stdVertex_eq_smul]

#audit_axioms mem_vstab_iff

/-- The conjugation `Pᵢ →* P₀`. -/
noncomputable def toStab0 (i : Fin 3) : vstab (A := A) (p := p) i →* vstab (A := A) (p := p) 0 where
  toFun γ := ⟨slConj (stdMat A p i) (γ : SL3 (Localization.Away p)),
    (mem_vstab_iff (A := A) (p := p) i (γ : SL3 (Localization.Away p))).mp γ.2⟩
  map_one' := Subtype.ext (map_one (slConj (stdMat A p i)))
  map_mul' γ δ :=
    Subtype.ext (map_mul (slConj (stdMat A p i)) (γ : SL3 (Localization.Away p)) δ)

@[simp] theorem coe_toStab0 (i : Fin 3) (γ : vstab (A := A) (p := p) i) :
    (toStab0 i γ : SL3 (Localization.Away p)) =
      slConj (stdMat A p i) (γ : SL3 (Localization.Away p)) :=
  rfl

variable (hinj : Function.Injective (algebraMap A (Localization.Away p)))
  (hstab0 : ∀ γ : SL3 (Localization.Away p), γ • stdVertex A p 0 = stdVertex A p 0 ↔
    ∀ k l, (γ : Matrix (Fin 3) (Fin 3) (Localization.Away p)) k l ∈
      Set.range (algebraMap A (Localization.Away p)))

include hstab0 in
/-- The entries of an element of `P₀`, in `A`. -/
theorem exists_entries (γ : vstab (A := A) (p := p) 0) :
    ∃ M : Matrix (Fin 3) (Fin 3) A,
      M.map (algebraMap A (Localization.Away p)) = (γ : Matrix (Fin 3) (Fin 3) _) := by
  have h : ∀ k l, ∃ a : A, algebraMap A (Localization.Away p) a =
      (γ : Matrix (Fin 3) (Fin 3) (Localization.Away p)) k l := fun k l => (hstab0 γ).mp γ.2 k l
  choose M hM using h
  exact ⟨M, Matrix.ext fun k l => hM k l⟩

#audit_axioms exists_entries

include hinj hstab0 in
theorem det_entries (γ : vstab (A := A) (p := p) 0) :
    (exists_entries hstab0 γ).choose.det = 1 := by
  apply hinj
  rw [RingHom.map_det, map_one]
  change ((exists_entries hstab0 γ).choose.map (algebraMap A (Localization.Away p))).det = 1
  rw [(exists_entries hstab0 γ).choose_spec]
  exact (γ : SL3 (Localization.Away p)).2

#audit_axioms det_entries

/-- `P₀ → SL₃(A)`: read the entries in `A`. -/
noncomputable def toA : vstab (A := A) (p := p) 0 →* SL3 A where
  toFun γ := ⟨(exists_entries hstab0 γ).choose, det_entries hinj hstab0 γ⟩
  map_one' := by
    apply Subtype.ext
    apply Matrix.map_injective hinj
    change ((exists_entries hstab0 1).choose).map (algebraMap A (Localization.Away p)) =
      (1 : Matrix (Fin 3) (Fin 3) A).map (algebraMap A (Localization.Away p))
    rw [(exists_entries hstab0 1).choose_spec]
    simp
  map_mul' γ δ := by
    apply Subtype.ext
    apply Matrix.map_injective hinj
    change ((exists_entries hstab0 (γ * δ)).choose).map (algebraMap A (Localization.Away p)) =
      ((exists_entries hstab0 γ).choose * (exists_entries hstab0 δ).choose).map
        (algebraMap A (Localization.Away p))
    rw [Matrix.map_mul, (exists_entries hstab0 (γ * δ)).choose_spec,
      (exists_entries hstab0 γ).choose_spec, (exists_entries hstab0 δ).choose_spec]
    rfl

theorem map_toA (γ : vstab (A := A) (p := p) 0) :
    ((toA hinj hstab0 γ : SL3 A) : Matrix (Fin 3) (Fin 3) A).map
      (algebraMap A (Localization.Away p)) = (γ : Matrix (Fin 3) (Fin 3) _) :=
  (exists_entries hstab0 γ).choose_spec

#audit_axioms map_toA

variable (hSL : Absorption.SpecialLinearInElementary A 3)

/-- `SL₃(A) →* E₃(A)`, from `SL₃(A) = E₃(A)`. -/
def slToE : SL3 A →* elementaryGroup (Fin 3) A :=
  Matrix.SpecialLinearGroup.toGL.codRestrict (elementaryGroup (Fin 3) A) fun γ =>
    hSL _ γ.2

@[simp] theorem coe_slToE (γ : SL3 A) :
    ((slToE hSL γ : elementaryGroup (Fin 3) A) : (Matrix (Fin 3) (Fin 3) A)ˣ) =
      Matrix.SpecialLinearGroup.toGL γ :=
  rfl

end Stab

section Local

variable {A : Type*} [CommRing A] {p : A}

theorem dgUnit_dvec (i : Fin 3) : dgUnit (dvec A p i) = stdMat A p i := by
  fin_cases i
  · apply Units.ext
    change Matrix.diagonal (fun k => (((1 : Fin 3 → (Localization.Away p)ˣ) k :
      (Localization.Away p)ˣ) : Localization.Away p)) = 1
    simp
  · rfl
  · rfl

#audit_axioms dgUnit_dvec

/-- Conjugating the projection of a twisted element back by `Dᵢ` gives the `A`-matrix. -/
theorem slConj_twist (i : Fin 3) (u : SteinbergGroup (Fin 3) A) :
    ((slConj (stdMat A p i) (elemToSL (projection
        (twist A p i (ringMap (algebraMap A (Localization.Away p)) u)))) : SL3 _) :
      Matrix (Fin 3) (Fin 3) (Localization.Away p)) =
      (((projection u : elementaryGroup (Fin 3) A) : (Matrix (Fin 3) (Fin 3) A)ˣ) :
        Matrix (Fin 3) (Fin 3) A).map (algebraMap A (Localization.Away p)) := by
  have h1 : ((projection (twist A p i (ringMap (algebraMap A (Localization.Away p)) u)) :
      elementaryGroup (Fin 3) (Localization.Away p)) : (Matrix (Fin 3) (Fin 3) _)ˣ) =
      stdMat A p i * elementaryMatrixUnitMap (algebraMap A (Localization.Away p))
        ((projection u : elementaryGroup (Fin 3) A) : (Matrix (Fin 3) (Fin 3) A)ˣ) *
        (stdMat A p i)⁻¹ := by
    rw [← dgUnit_dvec, twist, projection_dgHom, projection_ringMap, elementaryGroupMap_apply]
  have h2 : Matrix.SpecialLinearGroup.toGL (slConj (stdMat A p i) (elemToSL (projection
      (twist A p i (ringMap (algebraMap A (Localization.Away p)) u))))) =
      elementaryMatrixUnitMap (algebraMap A (Localization.Away p))
        ((projection u : elementaryGroup (Fin 3) A) : (Matrix (Fin 3) (Fin 3) A)ˣ) := by
    rw [toGL_slConj, toGL_elemToSL, h1]
    group
  exact congrArg Units.val h2

#audit_axioms slConj_twist

variable (hinj : Function.Injective (algebraMap A (Localization.Away p)))
  (hstab0 : ∀ γ : SL3 (Localization.Away p), γ • stdVertex A p 0 = stdVertex A p 0 ↔
    ∀ k l, (γ : Matrix (Fin 3) (Fin 3) (Localization.Away p)) k l ∈
      Set.range (algebraMap A (Localization.Away p)))
  (hSL : Absorption.SpecialLinearInElementary A 3)

include hstab0 in
/-- The projection of a twisted element lies in the stabilizer. -/
theorem twist_proj_mem (i : Fin 3) (u : SteinbergGroup (Fin 3) A) :
    elemToSL (projection (twist A p i (ringMap (algebraMap A (Localization.Away p)) u))) ∈
      vstab (A := A) (p := p) i := by
  rw [mem_vstab_iff]
  refine (hstab0 _).mpr fun k l =>
    ⟨(((projection u : elementaryGroup (Fin 3) A) : (Matrix (Fin 3) (Fin 3) A)ˣ) :
      Matrix (Fin 3) (Fin 3) A) k l, ?_⟩
  rw [slConj_twist]
  rfl

#audit_axioms twist_proj_mem

variable (N : Subgroup (SteinbergGroup (Fin 3) (Localization.Away p))) [N.Normal]
  (hN : ∀ i : Fin 3, ∀ k ∈ K2 (Fin 3) A,
    twist A p i (ringMap (algebraMap A (Localization.Away p)) k) ∈ N)

/-- `St₃(A) →* St₃(B)/N`, `u ↦ [δᵢ ι u]`. -/
noncomputable def twistQ (i : Fin 3) :
    SteinbergGroup (Fin 3) A →* SteinbergGroup (Fin 3) (Localization.Away p) ⧸ N :=
  (QuotientGroup.mk' N).comp ((twist A p i).comp (ringMap (algebraMap A (Localization.Away p))))

include hN in
theorem K2_le_ker_twistQ (i : Fin 3) : K2 (Fin 3) A ≤ (twistQ N i).ker := fun k hk =>
  (QuotientGroup.eq_one_iff _).mpr (hN i k hk)

#audit_axioms K2_le_ker_twistQ

/-- `E₃(A) →* St₃(B)/N`, through `E₃(A) ≅ St₃(A)/K₂(3, A)`. -/
noncomputable def psiQ (i : Fin 3) :
    elementaryGroup (Fin 3) A →* SteinbergGroup (Fin 3) (Localization.Away p) ⧸ N :=
  (QuotientGroup.lift (K2 (Fin 3) A) (twistQ N i) (K2_le_ker_twistQ N hN i)).comp
    (quotientK2Equiv (I := Fin 3) (R := A)).symm.toMonoidHom

theorem psiQ_projection (i : Fin 3) (u : SteinbergGroup (Fin 3) A) :
    psiQ N hN i (projection u) =
      (twist A p i (ringMap (algebraMap A (Localization.Away p)) u) :
        SteinbergGroup (Fin 3) (Localization.Away p) ⧸ N) := by
  have h : (quotientK2Equiv (I := Fin 3) (R := A)).symm (projection u) =
      (u : SteinbergGroup (Fin 3) A ⧸ K2 (Fin 3) A) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  change QuotientGroup.lift (K2 (Fin 3) A) (twistQ N i) (K2_le_ker_twistQ N hN i)
    ((quotientK2Equiv (I := Fin 3) (R := A)).symm (projection u)) = _
  rw [h, QuotientGroup.lift_mk]
  rfl

#audit_axioms psiQ_projection

/-- **The local homomorphism** `Pᵢ →* St₃(B)/N`. -/
noncomputable def localHom (i : Fin 3) :
    vstab (A := A) (p := p) i →* SteinbergGroup (Fin 3) (Localization.Away p) ⧸ N :=
  (psiQ N hN i).comp ((slToE hSL).comp ((toA hinj hstab0).comp (toStab0 i)))

/-- **On twisted elements, the local homomorphism is the quotient map.** -/
theorem localHom_twist (i : Fin 3) (u : SteinbergGroup (Fin 3) A) :
    localHom hinj hstab0 hSL N hN i ⟨_, twist_proj_mem hstab0 i u⟩ =
      (twist A p i (ringMap (algebraMap A (Localization.Away p)) u) :
        SteinbergGroup (Fin 3) (Localization.Away p) ⧸ N) := by
  have hA : slToE hSL (toA hinj hstab0 (toStab0 i ⟨_, twist_proj_mem hstab0 i u⟩)) =
      projection u := by
    apply Subtype.ext
    apply Units.ext
    change ((toA hinj hstab0 (toStab0 i ⟨_, twist_proj_mem hstab0 i u⟩) : SL3 A) :
      Matrix (Fin 3) (Fin 3) A) = ((projection u : elementaryGroup (Fin 3) A) :
        (Matrix (Fin 3) (Fin 3) A)ˣ)
    apply Matrix.map_injective hinj
    dsimp only
    rw [map_toA, coe_toStab0]
    dsimp only
    rw [slConj_twist]
  change psiQ N hN i (slToE hSL (toA hinj hstab0 (toStab0 i ⟨_, twist_proj_mem hstab0 i u⟩))) = _
  rw [hA, psiQ_projection]

#audit_axioms localHom_twist

/-- A lift of `γ ∈ Pᵢ` to `St₃(B)`, independent of `N`. -/
noncomputable def liftI (i : Fin 3) (γ : vstab (A := A) (p := p) i) :
    SteinbergGroup (Fin 3) (Localization.Away p) :=
  twist A p i (ringMap (algebraMap A (Localization.Away p))
    (projection_surjective (slToE hSL (toA hinj hstab0 (toStab0 i γ)))).choose)

theorem localHom_eq_mk_liftI (i : Fin 3) (γ : vstab (A := A) (p := p) i) :
    localHom hinj hstab0 hSL N hN i γ =
      (liftI hinj hstab0 hSL i γ : SteinbergGroup (Fin 3) (Localization.Away p) ⧸ N) := by
  change psiQ N hN i (slToE hSL (toA hinj hstab0 (toStab0 i γ))) = _
  rw [← (projection_surjective (slToE hSL (toA hinj hstab0 (toStab0 i γ)))).choose_spec,
    psiQ_projection]
  rfl

#audit_axioms localHom_eq_mk_liftI

end Local

end BTri
end BooneHigmanLinear
end GroupApproximation
