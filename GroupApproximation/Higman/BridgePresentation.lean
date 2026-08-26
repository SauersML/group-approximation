import GroupApproximation.Algebra.HNNCongr
import GroupApproximation.Algebra.HNNPresentation
import GroupApproximation.Algebra.PresentedGroupRelabel
import GroupApproximation.Higman.BridgeWordProblem
import GroupApproximation.Higman.RecursivePresentationBridge

/-!
# The effective HNN bridge, without an external presentation input

`BridgeWP.ExtPresentation` asks for a kernel presentation for every family
`g : ℕ → A`, even when that family does not generate `A`.  The bridge never
needs that stronger statement: its input includes

```
Subgroup.closure (Set.range g) = ⊤.
```

This file proves the presentation under precisely that hypothesis and closes
`BridgeEff.BridgeEffective` unconditionally.  The proof uses four existing
pieces:

* the presentation of a group by the kernel of a spanning family;
* the free-product presentation of `A * F₂`;
* `HNNPresentation.equivPres`;
* `HNNCongr.congrEquiv`, which transports the HNN extension across the base
  presentation.

The final presentation is numbered by `ℕ`.  Its relators are the old bridge
relators after the cyclic renaming `x ↦ 1`, `y ↦ 2`, `t ↦ 0`.  The old
relator set contains both orientations of every HNN relator; the presentation
theorem contains one orientation.  Their normal closures agree, which is the
only equality a presented group uses.
-/

namespace GroupApproximation
namespace Higman
namespace BridgePresentation

open GroupApproximation.Higman.HNNEmb
open GroupApproximation.Higman.BridgeEff
open GroupApproximation.Higman.BridgeWP

/-! ## 1. Numbering the base presentation -/

/-- Number the generators of `A * F₂` by putting `x,y` first and the family
of `A` afterwards. -/
def baseCode : (ℕ ⊕ Fin 2) ≃ ℕ where
  toFun
    | Sum.inl k => k + 2
    | Sum.inr i => i
  invFun n := if h : n < 2 then Sum.inr ⟨n, h⟩ else Sum.inl (n - 2)
  left_inv z := by
    cases z with
    | inl k =>
        simp [show ¬ k + 2 < 2 by omega]
    | inr i =>
        simp only [i.isLt, dite_true]
        exact congrArg Sum.inr (Fin.ext rfl)
  right_inv n := by
    by_cases h : n < 2
    · simp [h]
    · simp [h]
      omega

@[simp] theorem baseCode_inl (k : ℕ) : baseCode (Sum.inl k) = k + 2 := rfl

@[simp] theorem baseCode_inr (i : Fin 2) : baseCode (Sum.inr i) = i := rfl

/-- The relators before numbering: the word problem of `A` in the left block;
the free group has no relators. -/
def sumRels {A : Type} [Group A] (g : ℕ → A) : Set (FreeGroup (ℕ ⊕ Fin 2)) :=
  FreeGroup.map Sum.inl '' wordSet g ∪
    FreeGroup.map Sum.inr '' (∅ : Set (FreeGroup (Fin 2)))

/-- The same relators on the numbered base alphabet. -/
def baseRels {A : Type} [Group A] (g : ℕ → A) : Set (FreeGroup ℕ) :=
  PresentedGroupRelabel.relabelRels (baseCode : (ℕ ⊕ Fin 2) → ℕ) (sumRels g)

/-- The presentation with no relators is the free group. -/
def freePresentedEquiv (X : Type) :
    PresentedGroup (∅ : Set (FreeGroup X)) ≃* FreeGroup X :=
  MonoidHom.toMulEquiv
    (PresentedGroup.toGroup (fun _ h => False.elim h))
    (PresentedGroup.mk (∅ : Set (FreeGroup X)))
    (by
      refine PresentedGroup.ext fun x => ?_
      rw [MonoidHom.comp_apply, PresentedGroup.toGroup.of]
      rfl)
    (by
      refine FreeGroup.ext_hom _ _ fun x => ?_
      rw [MonoidHom.comp_apply]
      rfl)

@[simp] theorem freePresentedEquiv_of (X : Type) (x : X) :
    freePresentedEquiv X (PresentedGroup.of x) = FreeGroup.of x :=
  PresentedGroup.toGroup.of _

/-- Isomorphisms of both factors induce an isomorphism of their free products. -/
def coprodCongr {G H G' H' : Type} [Group G] [Group H] [Group G'] [Group H']
    (e : G ≃* G') (f : H ≃* H') :
    Monoid.Coprod G H ≃* Monoid.Coprod G' H' :=
  MonoidHom.toMulEquiv
    (Monoid.Coprod.lift
      (Monoid.Coprod.inl.comp e.toMonoidHom)
      (Monoid.Coprod.inr.comp f.toMonoidHom))
    (Monoid.Coprod.lift
      (Monoid.Coprod.inl.comp e.symm.toMonoidHom)
      (Monoid.Coprod.inr.comp f.symm.toMonoidHom))
    (by
      refine Monoid.Coprod.hom_ext ?_ ?_
      · refine MonoidHom.ext fun x => ?_
        simp only [MonoidHom.comp_apply, Monoid.Coprod.lift_apply_inl,
          MulEquiv.symm_apply_apply]
      · refine MonoidHom.ext fun x => ?_
        simp only [MonoidHom.comp_apply, Monoid.Coprod.lift_apply_inr,
          MulEquiv.symm_apply_apply])
    (by
      refine Monoid.Coprod.hom_ext ?_ ?_
      · refine MonoidHom.ext fun x => ?_
        simp only [MonoidHom.comp_apply, Monoid.Coprod.lift_apply_inl,
          MulEquiv.apply_symm_apply]
      · refine MonoidHom.ext fun x => ?_
        simp only [MonoidHom.comp_apply, Monoid.Coprod.lift_apply_inr,
          MulEquiv.apply_symm_apply])

@[simp] theorem coprodCongr_inl {G H G' H' : Type}
    [Group G] [Group H] [Group G'] [Group H']
    (e : G ≃* G') (f : H ≃* H') (x : G) :
    coprodCongr e f (Monoid.Coprod.inl x) = Monoid.Coprod.inl (e x) :=
  Monoid.Coprod.lift_apply_inl _ _ _

@[simp] theorem coprodCongr_inr {G H G' H' : Type}
    [Group G] [Group H] [Group G'] [Group H']
    (e : G ≃* G') (f : H ≃* H') (x : H) :
    coprodCongr e f (Monoid.Coprod.inr x) = Monoid.Coprod.inr (f x) :=
  Monoid.Coprod.lift_apply_inr _ _ _

/-- The whole word problem of a spanning family presents the group. -/
noncomputable def groupEquiv {A : Type} [Group A] (g : ℕ → A)
    (hspan : Subgroup.closure (Set.range g) = ⊤) :
    PresentedGroup (wordSet g) ≃* A := by
  change PresentedGroup (relatorSetOf g) ≃* A
  exact presentedGroupEquiv hspan

@[simp] theorem groupEquiv_of {A : Type} [Group A] (g : ℕ → A)
    (hspan : Subgroup.closure (Set.range g) = ⊤) (k : ℕ) :
    groupEquiv g hspan (PresentedGroup.of k) = g k := rfl

/-- The numbered presentation of `A * F₂`. -/
noncomputable def baseEquiv {A : Type} [Group A] (g : ℕ → A)
    (hspan : Subgroup.closure (Set.range g) = ⊤) :
    PresentedGroup (baseRels g) ≃* P A :=
  ((PresentedGroupRelabel.congrEquiv baseCode (sumRels g)).symm.trans
      (PresentedGroup.coprodPresentations (wordSet g)
        (∅ : Set (FreeGroup (Fin 2))))).trans
    (coprodCongr (groupEquiv g hspan) (freePresentedEquiv (Fin 2)))

@[simp] theorem baseEquiv_of_zero {A : Type} [Group A] (g : ℕ → A)
    (hspan : Subgroup.closure (Set.range g) = ⊤) :
    baseEquiv g hspan (PresentedGroup.of 0) = (xg : P A) := by
  change baseEquiv g hspan
      (PresentedGroup.of (baseCode (Sum.inr (0 : Fin 2)))) = _
  simp [baseEquiv, xg, iF]

@[simp] theorem baseEquiv_of_one {A : Type} [Group A] (g : ℕ → A)
    (hspan : Subgroup.closure (Set.range g) = ⊤) :
    baseEquiv g hspan (PresentedGroup.of 1) = (yg : P A) := by
  change baseEquiv g hspan
      (PresentedGroup.of (baseCode (Sum.inr (1 : Fin 2)))) = _
  simp [baseEquiv, yg, iF]

@[simp] theorem baseEquiv_of_add_two {A : Type} [Group A] (g : ℕ → A)
    (hspan : Subgroup.closure (Set.range g) = ⊤) (k : ℕ) :
    baseEquiv g hspan (PresentedGroup.of (k + 2)) = iA (g k) := by
  change baseEquiv g hspan
      (PresentedGroup.of (baseCode (Sum.inl k))) = _
  simp [baseEquiv, iA]

/-! ## 2. Transporting the associated subgroups -/

/-- The word naming `aᵢ` in the numbered base presentation. -/
def srcWord (i : ℕ) : FreeGroup ℕ :=
  FreeGroup.of 0 ^ (-(i : ℤ)) * FreeGroup.of 1 * FreeGroup.of 0 ^ (i : ℤ)

/-- The word naming `gᵢaᵢ`. -/
def tgtWord (i : ℕ) : FreeGroup ℕ :=
  FreeGroup.of (i + 2) * srcWord i

theorem baseEquiv_srcWord {A : Type} [Group A] (g : ℕ → A)
    (hspan : Subgroup.closure (Set.range g) = ⊤) (i : ℕ) :
    baseEquiv g hspan (PresentedGroup.mk (baseRels g) (srcWord i)) = aFam i := by
  unfold srcWord aFam
  simp only [map_mul, map_zpow, baseEquiv_of_zero, baseEquiv_of_one]

theorem baseEquiv_tgtWord {A : Type} [Group A] (g : ℕ → A)
    (hspan : Subgroup.closure (Set.range g) = ⊤) (i : ℕ) :
    baseEquiv g hspan (PresentedGroup.mk (baseRels g) (tgtWord i)) = bFam g i := by
  unfold tgtWord bFam
  rw [map_mul, baseEquiv_of_add_two, baseEquiv_srcWord]

/-- The actual-to-presented base isomorphism sends the source subgroup to the
source subgroup of `HNNPresentation`. -/
theorem map_Asub {A : Type} [Group A] (g : ℕ → A)
    (hspan : Subgroup.closure (Set.range g) = ⊤) :
    (Asub (A := A)).map (baseEquiv g hspan).symm.toMonoidHom =
      HNNPresentation.srcSub (baseRels g) srcWord := by
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    rw [Asub, aHom, range_lift] at hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        have he := baseEquiv_srcWord g hspan i
        have hv : (baseEquiv g hspan).symm (aFam i) =
            HNNPresentation.srcGen (baseRels g) srcWord i := by
          simpa [HNNPresentation.srcGen] using
            (congrArg (baseEquiv g hspan).symm he).symm
        rw [hv]
        exact HNNPresentation.srcGen_mem (baseRels g) srcWord i
    | one => simpa using Subgroup.one_mem (HNNPresentation.srcSub (baseRels g) srcWord)
    | mul x y _ _ hx hy => simpa using Subgroup.mul_mem _ hx hy
    | inv x _ hx => simpa using Subgroup.inv_mem _ hx
  · rw [HNNPresentation.srcSub, Subgroup.closure_le]
    rintro y ⟨i, rfl⟩
    refine ⟨aFam i, aFam_mem_Asub i, ?_⟩
    have he := congrArg (baseEquiv g hspan).symm (baseEquiv_srcWord g hspan i)
    simpa using he.symm

/-- The same transport for the target subgroup. -/
theorem map_Bsub {A : Type} [Group A] (g : ℕ → A)
    (hspan : Subgroup.closure (Set.range g) = ⊤) :
    (Bsub g).map (baseEquiv g hspan).symm.toMonoidHom =
      HNNPresentation.tgtSub (baseRels g) tgtWord := by
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    rw [Bsub, bHom, range_lift] at hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        have he := congrArg (baseEquiv g hspan).symm (baseEquiv_tgtWord g hspan i)
        have hv : (baseEquiv g hspan).symm (bFam g i) =
            HNNPresentation.tgtGen (baseRels g) tgtWord i := by
          simpa [HNNPresentation.tgtGen] using he.symm
        rw [hv]
        exact HNNPresentation.tgtGen_mem (baseRels g) tgtWord i
    | one => simpa using Subgroup.one_mem (HNNPresentation.tgtSub (baseRels g) tgtWord)
    | mul x y _ _ hx hy => simpa using Subgroup.mul_mem _ hx hy
    | inv x _ hx => simpa using Subgroup.inv_mem _ hx
  · rw [HNNPresentation.tgtSub, Subgroup.closure_le]
    rintro y ⟨i, rfl⟩
    refine ⟨bFam g i, bFam_mem_Bsub g i, ?_⟩
    have he := congrArg (baseEquiv g hspan).symm (baseEquiv_tgtWord g hspan i)
    simpa [HNNPresentation.tgtGen] using he.symm

theorem mem_Asub_iff {A : Type} [Group A] (g : ℕ → A)
    (hspan : Subgroup.closure (Set.range g) = ⊤) (x : P A) :
    x ∈ Asub ↔ (baseEquiv g hspan).symm x ∈
      HNNPresentation.srcSub (baseRels g) srcWord := by
  rw [← map_Asub g hspan, Subgroup.mem_map_equiv,
    MulEquiv.apply_symm_apply]

/-- The associated-subgroup isomorphism transported to the presented base. -/
noncomputable def presPhi {A : Type} [Group A] (g : ℕ → A)
    (hspan : Subgroup.closure (Set.range g) = ⊤) :
    HNNPresentation.srcSub (baseRels g) srcWord ≃*
      HNNPresentation.tgtSub (baseRels g) tgtWord :=
  (((MulEquiv.subgroupCongr (map_Asub g hspan)).symm.trans
      ((baseEquiv g hspan).symm.subgroupMap Asub).symm).trans (psi g)).trans
    (((baseEquiv g hspan).symm.subgroupMap (Bsub g)).trans
      (MulEquiv.subgroupCongr (map_Bsub g hspan)))

theorem presPhi_intertwines {A : Type} [Group A] (g : ℕ → A)
    (hspan : Subgroup.closure (Set.range g) = ⊤) :
    HNNCongr.Intertwines (psi g) (presPhi g hspan) (baseEquiv g hspan).symm
      (mem_Asub_iff g hspan) := by
  intro a ha
  have hsub : (⟨(baseEquiv g hspan)
      ((baseEquiv g hspan).symm a), by
        rw [MulEquiv.apply_symm_apply]
        exact ha⟩ : Asub) = ⟨a, ha⟩ :=
    Subtype.ext (MulEquiv.apply_symm_apply _ a)
  show (baseEquiv g hspan).symm
      ((psi g ⟨(baseEquiv g hspan) ((baseEquiv g hspan).symm a), _⟩ : Bsub g) : P A)
    = (baseEquiv g hspan).symm ((psi g ⟨a, ha⟩ : Bsub g) : P A)
  rw [hsub]

theorem presPhi_gen {A : Type} [Group A] (g : ℕ → A)
    (hspan : Subgroup.closure (Set.range g) = ⊤) (i : ℕ) :
    ((presPhi g hspan
        ⟨HNNPresentation.srcGen (baseRels g) srcWord i,
          HNNPresentation.srcGen_mem (baseRels g) srcWord i⟩ :
          HNNPresentation.tgtSub (baseRels g) tgtWord) :
        PresentedGroup (baseRels g)) =
      HNNPresentation.tgtGen (baseRels g) tgtWord i := by
  have hsrc : HNNPresentation.srcGen (baseRels g) srcWord i =
      (baseEquiv g hspan).symm (aFam i) := by
    have h := congrArg (baseEquiv g hspan).symm (baseEquiv_srcWord g hspan i)
    simpa [HNNPresentation.srcGen] using h.symm
  have hmem : aFam i ∈ Asub := aFam_mem_Asub i
  have hsub : (⟨HNNPresentation.srcGen (baseRels g) srcWord i,
      HNNPresentation.srcGen_mem (baseRels g) srcWord i⟩ :
        HNNPresentation.srcSub (baseRels g) srcWord) =
      ⟨(baseEquiv g hspan).symm (aFam i), (mem_Asub_iff g hspan (aFam i)).1 hmem⟩ :=
    Subtype.ext hsrc
  rw [hsub, presPhi_intertwines g hspan (aFam i) hmem, psi_aFam]
  have h := congrArg (baseEquiv g hspan).symm (baseEquiv_tgtWord g hspan i)
  simpa [HNNPresentation.tgtGen] using h.symm

/-! ## 3. The presented extension and its numbered relators -/

/-- Add one stable letter to a countable alphabet. -/
def optionNatEquiv : Option ℕ ≃ ℕ where
  toFun
    | none => 0
    | some n => n + 1
  invFun
    | 0 => none
    | n + 1 => some n
  left_inv x := by cases x <;> rfl
  right_inv n := by cases n <;> rfl

@[simp] theorem optionNatEquiv_none : optionNatEquiv none = 0 := rfl

@[simp] theorem optionNatEquiv_some (n : ℕ) : optionNatEquiv (some n) = n + 1 := rfl

/-- The relators supplied literally by `HNNPresentation`, numbered by `ℕ`. -/
def hnnNumberedRels {A : Type} [Group A] (g : ℕ → A) : Set (FreeGroup ℕ) :=
  PresentedGroupRelabel.relabelRels (optionNatEquiv : Option ℕ → ℕ)
    (HNNPresentation.hnnRels (baseRels g) srcWord tgtWord)

/-- The cyclic renaming from the old bridge convention `(x,y,t)` to the
presentation convention `(t,x,y)`. -/
def cycle (k : ℕ) : ℕ := if k < 3 then (k + 1) % 3 else k

@[simp] theorem cycle_zero : cycle 0 = 1 := by decide
@[simp] theorem cycle_one : cycle 1 = 2 := by decide
@[simp] theorem cycle_two : cycle 2 = 0 := by decide
theorem cycle_add_three (k : ℕ) : cycle (k + 3) = k + 3 := by
  simp [cycle, show ¬ k + 3 < 3 by omega]

/-- The enumerable, symmetric relator set used for the recursive presentation. -/
def codedRels {A : Type} [Group A] (g : ℕ → A) : Set (FreeGroup ℕ) :=
  FreeGroup.map cycle '' relSet g

theorem srcWord_succ (i : ℕ) :
    srcWord (i + 1) = (FreeGroup.of 0)⁻¹ * (srcWord i * FreeGroup.of 0) := by
  unfold srcWord
  push_cast
  group

theorem freeEval_aRaw (i : ℕ) : freeEval (aRaw i) = srcWord i := by
  induction i with
  | zero =>
      unfold freeEval srcWord
      simp
  | succ i ih =>
      rw [aRaw_succ]
      unfold freeEval at ih ⊢
      rw [evalRaw_cons, evalRaw_append, ih, srcWord_succ]
      simp

/-- A numbered HNN relator is the cyclic relabelling of the old raw relator. -/
theorem map_cycle_hnnRaw (i : ℕ) :
    FreeGroup.map cycle (freeEval (hnnRaw i)) =
      FreeGroup.map optionNatEquiv
        (HNNPresentation.stableWord * HNNPresentation.emb (srcWord i) *
          HNNPresentation.stableWord⁻¹ *
          (HNNPresentation.emb (tgtWord i))⁻¹) := by
  have hsrc : FreeGroup.map cycle (srcWord i) =
      FreeGroup.map (fun k : ℕ => k + 1) (srcWord i) := by
    unfold srcWord
    simp only [map_mul, map_zpow, FreeGroup.map.of, cycle_zero, cycle_one]
  have hold : freeEval (hnnRaw i) =
      FreeGroup.of 2 * srcWord i * (FreeGroup.of 2)⁻¹ *
        (FreeGroup.of (i + 3) * srcWord i)⁻¹ := by
    unfold hnnRaw freeEval
    rw [evalRaw_append]
    simp only [evalRaw_cons, evalRaw_invRaw, freeEval_aRaw]
    group
  rw [hold]
  simp only [map_mul, map_inv, FreeGroup.map.of, cycle_two, cycle_add_three,
    HNNPresentation.stableWord, HNNPresentation.emb, optionNatEquiv_none,
    optionNatEquiv_some, tgtWord, hsrc]

theorem numbered_base_relator {A : Type} [Group A] (g : ℕ → A)
    (u : FreeGroup ℕ) :
    FreeGroup.map optionNatEquiv
        (HNNPresentation.emb (FreeGroup.map (fun k : ℕ => k + 2) u)) =
      FreeGroup.map cycle (FreeGroup.map (fun k : ℕ => k + 3) u) := by
  have hhom :
      (FreeGroup.map optionNatEquiv).comp
          (HNNPresentation.emb.comp (FreeGroup.map (fun k : ℕ => k + 2))) =
        (FreeGroup.map cycle).comp (FreeGroup.map (fun k : ℕ => k + 3)) := by
    apply FreeGroup.ext_hom
    intro k
    simp only [MonoidHom.comp_apply, FreeGroup.map.of, HNNPresentation.emb,
      optionNatEquiv_some, cycle_add_three]
  exact DFunLike.congr_fun hhom u

/-- Every literal HNN-presentation relator occurs among `codedRels`. -/
theorem hnnNumberedRels_subset_coded {A : Type} [Group A] (g : ℕ → A) :
    hnnNumberedRels g ⊆ codedRels g := by
  rintro r ⟨s, hs, rfl⟩
  rcases hs with ⟨u, ⟨v, hv, rfl⟩, rfl⟩ | ⟨i, rfl⟩
  · refine ⟨FreeGroup.map (fun k : ℕ => k + 3) v, Or.inl ⟨v, hv, rfl⟩, ?_⟩
    exact numbered_base_relator g v
  · refine ⟨freeEval (hnnRaw i), Or.inr ⟨2 * i, ?_⟩, ?_⟩
    · rw [hnnFam_even (n := 2 * i) (by omega)]
      congr 2
      omega
    · exact (map_cycle_hnnRaw i).symm

/-- Conversely, every symmetric coded relator belongs to the normal closure
of the literal HNN relators. -/
theorem codedRels_subset_normalClosure {A : Type} [Group A] (g : ℕ → A) :
    codedRels g ⊆ Subgroup.normalClosure (hnnNumberedRels g) := by
  rintro r ⟨s, hs, rfl⟩
  rcases hs with ⟨u, hu, rfl⟩ | ⟨n, rfl⟩
  · refine Subgroup.subset_normalClosure ?_
    refine ⟨FreeGroup.map optionNatEquiv
      (HNNPresentation.emb (FreeGroup.map (fun k : ℕ => k + 2) u)), ?_, ?_⟩
    · exact Or.inl ⟨FreeGroup.map (fun k : ℕ => k + 2) u,
        ⟨u, hu, rfl⟩, rfl⟩
    · exact (numbered_base_relator g u).symm
  · by_cases h : n % 2 = 0
    · rw [hnnFam_even h, map_cycle_hnnRaw]
      exact Subgroup.subset_normalClosure
        ⟨_, Or.inr ⟨n / 2, rfl⟩, rfl⟩
    · rw [hnnFam_odd h, freeEval_invRaw, map_inv, map_cycle_hnnRaw]
      exact Subgroup.inv_mem _ (Subgroup.subset_normalClosure
        ⟨_, Or.inr ⟨n / 2, rfl⟩, rfl⟩)

theorem normalClosure_numbered_eq_coded {A : Type} [Group A] (g : ℕ → A) :
    Subgroup.normalClosure (hnnNumberedRels g) =
      Subgroup.normalClosure (codedRels g) := by
  apply le_antisymm
  · exact Subgroup.normalClosure_mono (hnnNumberedRels_subset_coded g)
  · exact Subgroup.normalClosure_le_normal (codedRels_subset_normalClosure g)

/-- Equality of normal closures induces equality of the presented groups. -/
def normalClosureEquiv {S T : Set (FreeGroup ℕ)}
    (h : Subgroup.normalClosure S = Subgroup.normalClosure T) :
    PresentedGroup S ≃* PresentedGroup T :=
  QuotientGroup.quotientMulEquivOfEq h

@[simp] theorem normalClosureEquiv_mk {S T : Set (FreeGroup ℕ)}
    (h : Subgroup.normalClosure S = Subgroup.normalClosure T) (w : FreeGroup ℕ) :
    normalClosureEquiv h (PresentedGroup.mk S w) = PresentedGroup.mk T w := rfl

/-! ## 4. The extension is the coded presentation -/

/-- The actual HNN extension, transported to the presented base and then to
the numbered relator set. -/
noncomputable def extEquivNumbered {A : Type} [Group A] (g : ℕ → A)
    (hspan : Subgroup.closure (Set.range g) = ⊤) :
    Ext g ≃* PresentedGroup (hnnNumberedRels g) :=
  ((HNNCongr.congrEquiv (psi g) (presPhi g hspan) (baseEquiv g hspan).symm
      (mem_Asub_iff g hspan) (presPhi_intertwines g hspan)).trans
    (HNNPresentation.equivPres (baseRels g) srcWord tgtWord (presPhi g hspan)
      (presPhi_gen g hspan)).symm).trans
    (PresentedGroupRelabel.congrEquiv optionNatEquiv
      (HNNPresentation.hnnRels (baseRels g) srcWord tgtWord))

/-- The final equivalence to the symmetric enumerable presentation. -/
noncomputable def extEquivCoded {A : Type} [Group A] (g : ℕ → A)
    (hspan : Subgroup.closure (Set.range g) = ⊤) :
    Ext g ≃* PresentedGroup (codedRels g) :=
  (extEquivNumbered g hspan).trans
    (normalClosureEquiv (normalClosure_numbered_eq_coded g))

theorem extEquivNumbered_t {A : Type} [Group A] (g : ℕ → A)
    (hspan : Subgroup.closure (Set.range g) = ⊤) :
    extEquivNumbered g hspan (HNNExtension.t : Ext g) = PresentedGroup.of 0 := by
  simp [extEquivNumbered, HNNPresentation.equivPres, HNNPresentation.bwd,
    HNNCongr.congrEquiv, PresentedGroupRelabel.congrEquiv]

theorem extEquivNumbered_x {A : Type} [Group A] (g : ℕ → A)
    (hspan : Subgroup.closure (Set.range g) = ⊤) :
    extEquivNumbered g hspan (HNNExtension.of (xg : P A)) = PresentedGroup.of 1 := by
  simp [extEquivNumbered, HNNPresentation.equivPres, HNNPresentation.bwd,
    HNNPresentation.bwdBase_mk, HNNCongr.congrEquiv, baseEquiv_of_zero,
    PresentedGroupRelabel.congrEquiv]

theorem extEquivNumbered_y {A : Type} [Group A] (g : ℕ → A)
    (hspan : Subgroup.closure (Set.range g) = ⊤) :
    extEquivNumbered g hspan (HNNExtension.of (yg : P A)) = PresentedGroup.of 2 := by
  simp [extEquivNumbered, HNNPresentation.equivPres, HNNPresentation.bwd,
    HNNPresentation.bwdBase_mk, HNNCongr.congrEquiv, baseEquiv_of_one,
    PresentedGroupRelabel.congrEquiv]

theorem extEquivCoded_gen3 {A : Type} [Group A] (g : ℕ → A)
    (hspan : Subgroup.closure (Set.range g) = ⊤) (j : Fin 3) :
    extEquivCoded g hspan (gen3 g j) =
      PresentedGroup.of ((j.1 + 1) % 3) := by
  fin_cases j <;>
    simp [extEquivCoded, gen3, extEquivNumbered_x, extEquivNumbered_y,
      extEquivNumbered_t]

theorem pi3_to_coded {A : Type} [Group A] (g : ℕ → A)
    (hspan : Subgroup.closure (Set.range g) = ⊤) (v : RawWord) :
    extEquivCoded g hspan (pi3 g (rawToFree 2 v)) =
      evalRaw (fun k ↦ (PresentedGroup.of k : PresentedGroup (codedRels g)))
        (relabel (fun k ↦ (k + 1) % 3) v) := by
  rw [lift_rawToFree]
  change extEquivCoded g hspan
      (evalRaw (fun k : ℕ ↦ gen3 g ⟨k % 3, Nat.mod_lt _ (by omega)⟩) v) = _
  rw [map_evalRaw, evalRaw_relabel]
  refine congrArg (fun f : ℕ → PresentedGroup (codedRels g) ↦ evalRaw f v) ?_
  funext k
  rw [extEquivCoded_gen3]
  congr 1
  omega

/-! ## 5. Enumerability and the unconditional bridge -/

theorem primrec_cycle : Primrec cycle := by
  have hlt : PrimrecPred fun k : ℕ ↦ k < 3 := Primrec.nat_lt.comp Primrec.id (Primrec.const 3)
  have hnext : Primrec fun k : ℕ ↦ (k + 1) % 3 :=
    Primrec.nat_mod.comp
      (Primrec.nat_add.comp Primrec.id (Primrec.const 1)) (Primrec.const 3)
  exact Primrec.cond hlt.decide hnext Primrec.id

theorem inv_mem_codedRels {A : Type} [Group A] (g : ℕ → A)
    {z : FreeGroup ℕ} (hz : z ∈ codedRels g) : z⁻¹ ∈ codedRels g := by
  obtain ⟨x, hx, rfl⟩ := hz
  refine ⟨x⁻¹, inv_mem_relSet g hx, map_inv _ _⟩

theorem symmetrize_codedRels {A : Type} [Group A] (g : ℕ → A) :
    symmetrize (codedRels g) = codedRels g := by
  refine Set.union_eq_self_of_subset_right ?_
  rintro _ ⟨z, hz, rfl⟩
  exact inv_mem_codedRels g hz

theorem search_codedRels {A : Type} [Group A] (g : ℕ → A)
    (hre : REPred fun w : RawWord ↦ evalRaw g w = 1) :
    ∃ f : RawWord → ℕ → Bool, Primrec₂ f ∧
      ∀ v : RawWord, freeEval v ∈ symmetrize (codedRels g) ↔
        ∃ n, f v n = true := by
  obtain ⟨f, hf, hspec⟩ := search_relSet g hre
  obtain ⟨F, hF, hFspec⟩ := search_image primrec_cycle hf hspec
  obtain ⟨F', hF', hF'spec⟩ := search_reindex F hF
  refine ⟨F', hF', fun v ↦ ?_⟩
  rw [symmetrize_codedRels]
  exact hFspec v |>.trans (hF'spec v)

theorem rePred_pi3_of_spans {A : Type} [Group A] (g : ℕ → A)
    (hspan : Subgroup.closure (Set.range g) = ⊤)
    (hre : REPred fun w : RawWord ↦ evalRaw g w = 1) :
    REPred fun v : RawWord ↦ pi3 g (rawToFree 2 v) = 1 := by
  obtain ⟨f, hf, hspec⟩ := search_codedRels g hre
  have hcanonical : REPred fun w : RawWord ↦
      evalRaw (fun k ↦ (PresentedGroup.of k : PresentedGroup (codedRels g))) w = 1 :=
    rePred_wordProblem_of_relators f _ (codedRels g)
      (evalRaw_presentedGroup_eq_one_iff (codedRels g)) hf hspec
  have hrotate : Computable fun v : RawWord ↦ relabel (fun k ↦ (k + 1) % 3) v := by
    exact (primrec_relabel
      (Primrec.nat_mod.comp
        (Primrec.nat_add.comp Primrec.id (Primrec.const 1)) (Primrec.const 3))).to_comp
  refine (rePred_comp hcanonical hrotate).of_eq fun v ↦ ?_
  rw [← pi3_to_coded g hspan]
  exact (extEquivCoded g hspan).map_eq_one_iff.symm

/-- **The repaired bridge is unconditional.**  This is the direct replacement
for the old route through the overstrong `BridgeWP.ExtPresentation` input. -/
theorem bridgeEffective : BridgeEffective where
  recursive := by
    intro A _ g hspan hre
    exact ⟨fgRecursiveExt g hspan (rePred_pi3_of_spans g hspan hre)⟩

end BridgePresentation
end Higman
end GroupApproximation
