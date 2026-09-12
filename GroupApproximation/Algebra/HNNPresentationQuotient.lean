import GroupApproximation.Algebra.HNNPresentation

/-!
# Regrouping an HNN presentation as a quotient of a free product

`HNNPresentation.Pres R w v` is written as one presented group on the alphabet
`Option X`.  This file records the equivalent two-stage description: first
form the group presented by `R`, freely adjoin an infinite cyclic generator,
and then quotient by the displayed conjugation relators.  Unlike
`HNNPresentation.equivPres`, this statement does not require the displayed
source and target families to generate isomorphic subgroups.
-/

namespace GroupApproximation
namespace HNNPresentationQuotient

open Monoid

variable {X I : Type} (rels : Set (FreeGroup X)) (w v : I → FreeGroup X)

section Transport

variable {G H : Type} [Group G] [Group H]

/-- An equivalence of base groups extends across the freely adjoined stable
letter. -/
def coprodCongr (e : G ≃* H) :
    Coprod G (Multiplicative ℤ) ≃* Coprod H (Multiplicative ℤ) := by
  let f : Coprod G (Multiplicative ℤ) →* Coprod H (Multiplicative ℤ) :=
    Coprod.lift (Coprod.inl.comp e.toMonoidHom) Coprod.inr
  let g : Coprod H (Multiplicative ℤ) →* Coprod G (Multiplicative ℤ) :=
    Coprod.lift (Coprod.inl.comp e.symm.toMonoidHom) Coprod.inr
  refine MonoidHom.toMulEquiv f g ?_ ?_
  · refine Coprod.hom_ext ?_ ?_
    · ext x
      simp [f, g]
    · ext
      simp [f, g]
  · refine Coprod.hom_ext ?_ ?_
    · ext x
      simp [f, g]
    · ext
      simp [f, g]

@[simp] theorem coprodCongr_inl (e : G ≃* H) (g : G) :
    coprodCongr e (Coprod.inl g) = Coprod.inl (e g) := by
  simp [coprodCongr]

@[simp] theorem coprodCongr_inr (e : G ≃* H) (z : Multiplicative ℤ) :
    coprodCongr e (Coprod.inr z) = Coprod.inr z := by
  simp [coprodCongr]

/-- A group equivalence transports a quotient by a normally generated set to
the quotient by the image set. -/
noncomputable def quotientEquivImage (e : G ≃* H) (S : Set G) :
    (G ⧸ Subgroup.normalClosure S) ≃*
      H ⧸ Subgroup.normalClosure (e '' S) := by
  let qG := QuotientGroup.mk' (Subgroup.normalClosure S)
  let qH := QuotientGroup.mk' (Subgroup.normalClosure (e '' S))
  let f : G ⧸ Subgroup.normalClosure S →*
      H ⧸ Subgroup.normalClosure (e '' S) :=
    QuotientGroup.lift _ (qH.comp e.toMonoidHom) (by
      refine Subgroup.normalClosure_le_normal ?_
      intro x hx
      exact (QuotientGroup.eq_one_iff _).2
        (Subgroup.subset_normalClosure ⟨x, hx, rfl⟩))
  let g : H ⧸ Subgroup.normalClosure (e '' S) →*
      G ⧸ Subgroup.normalClosure S :=
    QuotientGroup.lift _ (qG.comp e.symm.toMonoidHom) (by
      refine Subgroup.normalClosure_le_normal ?_
      rintro _ ⟨x, hx, rfl⟩
      exact (QuotientGroup.eq_one_iff _).2 (by
        simpa using Subgroup.subset_normalClosure hx))
  refine MonoidHom.toMulEquiv f g ?_ ?_
  · refine MonoidHom.ext fun x => ?_
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective
      (Subgroup.normalClosure S) x
    change qG (e.symm (e x)) = qG x
    rw [e.symm_apply_apply]
  · refine MonoidHom.ext fun x => ?_
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective
      (Subgroup.normalClosure (e '' S)) x
    change qH (e (e.symm x)) = qH x
    rw [e.apply_symm_apply]

@[simp] theorem quotientEquivImage_mk (e : G ≃* H) (S : Set G) (g : G) :
    quotientEquivImage e S (QuotientGroup.mk' (Subgroup.normalClosure S) g) =
      QuotientGroup.mk' (Subgroup.normalClosure (e '' S)) (e g) := rfl

end Transport

/-- The free product of the already-presented base with the stable letter. -/
abbrev Amb : Type := Coprod (PresentedGroup rels) (Multiplicative ℤ)

/-- The stable letter in the free-product model. -/
def tAmb : Amb rels := Coprod.inr (Multiplicative.ofAdd 1)

/-- The displayed conjugation relator in the free-product model. -/
def relator (i : I) : Amb rels :=
  tAmb rels * Coprod.inl (PresentedGroup.mk rels (w i)) * (tAmb rels)⁻¹ *
    (Coprod.inl (PresentedGroup.mk rels (v i)))⁻¹

/-- The family of displayed conjugation relators. -/
def relators : Set (Amb rels) := Set.range (relator rels w v)

/-- The raw quotient of the free product by the displayed relations. -/
abbrev Q : Type := Amb rels ⧸ Subgroup.normalClosure (relators rels w v)

/-- The already-presented base inside the quotient. -/
def qBase : PresentedGroup rels →* Q rels w v :=
  (QuotientGroup.mk' (Subgroup.normalClosure (relators rels w v))).comp Coprod.inl

/-- The stable letter inside the quotient. -/
def qT : Q rels w v :=
  QuotientGroup.mk' (Subgroup.normalClosure (relators rels w v)) (tAmb rels)

/-- Images of the one-stage presentation's generators in the two-stage quotient. -/
def fwdGen : Option X → Q rels w v
  | none => qT rels w v
  | some x => qBase rels w v (PresentedGroup.of x)

theorem lift_fwdGen_emb (r : FreeGroup X) :
    FreeGroup.lift (fwdGen rels w v) (HNNPresentation.emb r) =
      qBase rels w v (PresentedGroup.mk rels r) := by
  rw [← MonoidHom.comp_apply, HNNPresentation.lift_emb]
  show FreeGroup.lift (fun x => qBase rels w v (PresentedGroup.of x)) r = _
  rw [HNNPresentation.lift_comp, MonoidHom.comp_apply,
    HNNPresentation.lift_of_eq_mk]

theorem fwd_rels : ∀ r ∈ HNNPresentation.hnnRels rels w v,
    FreeGroup.lift (fwdGen rels w v) r = 1 := by
  rintro r (⟨r₀, hr₀, rfl⟩ | ⟨i, rfl⟩)
  · rw [lift_fwdGen_emb,
      PresentedGroup.mk_eq_one_iff.2 (Subgroup.subset_normalClosure hr₀), map_one]
  · show FreeGroup.lift (fwdGen rels w v)
        (HNNPresentation.stableWord * HNNPresentation.emb (w i) *
          HNNPresentation.stableWord⁻¹ * (HNNPresentation.emb (v i))⁻¹) = 1
    simp only [map_mul, map_inv, lift_fwdGen_emb]
    change qT rels w v * qBase rels w v (PresentedGroup.mk rels (w i)) *
      (qT rels w v)⁻¹ *
      (qBase rels w v (PresentedGroup.mk rels (v i)))⁻¹ = 1
    exact (QuotientGroup.eq_one_iff _).2
      (Subgroup.subset_normalClosure ⟨i, rfl⟩)

/-- The map from the one-stage HNN presentation to the two-stage quotient. -/
def fwd : HNNPresentation.Pres rels w v →* Q rels w v :=
  PresentedGroup.toGroup (fwd_rels rels w v)

/-- The free product maps back to the one-stage presentation. -/
def preToPres : Amb rels →* HNNPresentation.Pres rels w v :=
  Coprod.lift (HNNPresentation.bwdBase rels w v)
    (zpowersHom _ (PresentedGroup.of none))

@[simp] theorem preToPres_inl (g : PresentedGroup rels) :
    preToPres rels w v (Coprod.inl g) = HNNPresentation.bwdBase rels w v g :=
  Coprod.lift_apply_inl _ _ _

@[simp] theorem preToPres_tAmb :
    preToPres rels w v (tAmb rels) =
      (PresentedGroup.of none : HNNPresentation.Pres rels w v) := by
  simp [preToPres, tAmb]

theorem preToPres_relator (i : I) :
    preToPres rels w v (relator rels w v i) = 1 := by
  simp only [relator, map_mul, map_inv, preToPres_inl, preToPres_tAmb]
  have h := HNNPresentation.bwd_hgen rels w v i
  unfold HNNPresentation.srcGen HNNPresentation.tgtGen at h
  rw [h]
  group

theorem normalClosure_relators_le_ker :
    Subgroup.normalClosure (relators rels w v) ≤ (preToPres rels w v).ker := by
  refine Subgroup.normalClosure_le_normal ?_
  rintro _ ⟨i, rfl⟩
  exact preToPres_relator rels w v i

/-- The map from the two-stage quotient back to the one-stage presentation. -/
def bwd : Q rels w v →* HNNPresentation.Pres rels w v :=
  QuotientGroup.lift _ (preToPres rels w v)
    (normalClosure_relators_le_ker rels w v)

@[simp] theorem fwd_of_some (x : X) :
    fwd rels w v (PresentedGroup.of (some x)) =
      qBase rels w v (PresentedGroup.of x) :=
  PresentedGroup.toGroup.of (fwd_rels rels w v)

@[simp] theorem fwd_of_none :
    fwd rels w v (PresentedGroup.of none) = qT rels w v :=
  PresentedGroup.toGroup.of (fwd_rels rels w v)

@[simp] theorem bwd_mk (x : Amb rels) :
    bwd rels w v
        (QuotientGroup.mk' (Subgroup.normalClosure (relators rels w v)) x) =
      preToPres rels w v x := rfl

theorem bwd_fwd :
    (bwd rels w v).comp (fwd rels w v) = MonoidHom.id _ := by
  refine PresentedGroup.ext fun x => ?_
  cases x with
  | none =>
      rw [MonoidHom.comp_apply, fwd_of_none, qT, bwd_mk, preToPres_tAmb]
      rfl
  | some x =>
      rw [MonoidHom.comp_apply, fwd_of_some, qBase, MonoidHom.comp_apply,
        bwd_mk, preToPres_inl]
      exact HNNPresentation.bwdBase_mk rels w v (FreeGroup.of x)

theorem fwd_bwd :
    (fwd rels w v).comp (bwd rels w v) = MonoidHom.id _ := by
  have key : ((fwd rels w v).comp (bwd rels w v)).comp
      (QuotientGroup.mk' (Subgroup.normalClosure (relators rels w v))) =
      (MonoidHom.id (Q rels w v)).comp
        (QuotientGroup.mk' (Subgroup.normalClosure (relators rels w v))) := by
    refine Coprod.hom_ext ?_ ?_
    · refine MonoidHom.ext fun g => ?_
      induction g using PresentedGroup.induction_on with
      | _ r =>
          change fwd rels w v
              (bwd rels w v
                (QuotientGroup.mk' (Subgroup.normalClosure (relators rels w v))
                  (Coprod.inl (PresentedGroup.mk rels r)))) =
            QuotientGroup.mk' (Subgroup.normalClosure (relators rels w v))
              (Coprod.inl (PresentedGroup.mk rels r))
          rw [bwd_mk, preToPres_inl, HNNPresentation.bwdBase_mk]
          have hf : (fwd rels w v).comp
              (PresentedGroup.mk (HNNPresentation.hnnRels rels w v)) =
              FreeGroup.lift (fwdGen rels w v) := by
            refine FreeGroup.ext_hom _ _ fun x => ?_
            cases x with
            | none => exact fwd_of_none rels w v
            | some x => exact fwd_of_some rels w v x
          rw [← MonoidHom.comp_apply, hf, lift_fwdGen_emb]
          rfl
    · refine MonoidHom.ext_mint ?_
      rw [MonoidHom.comp_apply, MonoidHom.comp_apply]
      change fwd rels w v
          (bwd rels w v
            (QuotientGroup.mk' (Subgroup.normalClosure (relators rels w v))
              (tAmb rels))) = _
      rw [bwd_mk, preToPres_tAmb, fwd_of_none]
      rfl
  refine MonoidHom.ext fun q => ?_
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective
    (Subgroup.normalClosure (relators rels w v)) q
  exact congrArg (fun h : Amb rels →* Q rels w v => h x) key

/-- **Regroup an HNN presentation without assuming an edge-subgroup
isomorphism.** -/
noncomputable def equiv :
    HNNPresentation.Pres rels w v ≃* Q rels w v where
  toFun := fwd rels w v
  invFun := bwd rels w v
  left_inv x := congrArg
    (fun h : HNNPresentation.Pres rels w v →* HNNPresentation.Pres rels w v => h x)
    (bwd_fwd rels w v)
  right_inv x := congrArg (fun h : Q rels w v →* Q rels w v => h x)
    (fwd_bwd rels w v)
  map_mul' := map_mul _

@[simp] theorem equiv_oldGenerator (x : X) :
    equiv rels w v (PresentedGroup.of (some x)) =
      qBase rels w v (PresentedGroup.of x) :=
  fwd_of_some rels w v x

@[simp] theorem equiv_stable :
    equiv rels w v (PresentedGroup.of none) = qT rels w v :=
  fwd_of_none rels w v

end HNNPresentationQuotient
end GroupApproximation
