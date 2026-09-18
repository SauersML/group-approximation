import GroupApproximation.Manuscript.NonMFNotes.Full.Exactness.FreeProductPropertyA
import GroupApproximation.Analysis.PropertyAExtension
import GroupApproximation.Analysis.PropertyAFiniteKernel
import GroupApproximation.Analysis.PropertyALocality
import GroupApproximation.Sofic.LiteralSoficAssembly

/-!
# The block Clifford group `C(𝒢)` has property A

Source: `non_mf_group_notes.tex`, section `sec:Esofic`, paragraph
"Exactness."  The paragraph argues:

1. `C(𝒢)/⟨ζ⟩` is an increasing union of finite free products `Q_n` of
   elementary abelian `2`-groups, and each `Q_n` is exact (Dykema);
2. exactness passes to increasing unions (Kirchberg--Wassermann);
3. `⟨ζ⟩` is finite, so exactness passes up to `C(𝒢)`.

This file proves the group-level content of steps 1--3 unconditionally, with
property A (`ExactnessPermanence.HasPropertyA`) as the exactness predicate.

* Step 1 at the printed instance is `hasPropertyA_coprodI`
  (`FreeProductPropertyA.lean`).
* A window over all sites of a finite set of blocks `J` maps onto the free
  product `∗_{j ∈ J} (ℤ/2)^{B j}` (`windowMap_surjective`), with kernel inside
  `{1, ζ}` (`finite_ker_windowMap`).  Finite-kernel permanence then gives
  `hasPropertyA_window`.  This merges steps 1 and 3 window by window.
* The windows over full blocks are directed and cover `C(𝒢)`, so locality
  (step 2) gives `hasPropertyA_blockClifford`.
* `hasPropertyA_lampFactor` transports this to the literal lamp factor of the
  manuscript's group through `LiteralSoficAssembly.lampEquiv`.

## Not proved here

The remaining links of the paragraph are not claimed:

* property A for the linear group `Σ ≤ GL₄(ℚ)` (Guentner--Higson--Weinberger);
* the crossover from group exactness to exactness of `C*_red`
  (Kirchberg--Wassermann / Ozawa).
-/

namespace GroupApproximation.Full.NN09

open BlockCliffordLamp BlockCliffordTowerSofic FreeProductSignReflection

section BlockClifford

variable (I : Type) (B : I → Type) [∀ i, DecidableEq (B i)] [∀ i, Fintype (B i)]

/-- All sites lying over a finite set of blocks. -/
def fullSites (J : Finset I) : Finset ((i : I) × B i) :=
  J.sigma fun _ => Finset.univ

omit [(i : I) → DecidableEq (B i)] in
theorem fullSites_mono {J J' : Finset I} (h : J ⊆ J') :
    fullSites I B J ⊆ fullSites I B J' := by
  intro p hp
  rw [fullSites, Finset.mem_sigma] at hp ⊢
  exact ⟨h hp.1, hp.2⟩

omit [(i : I) → DecidableEq (B i)] in
theorem subset_fullSites [DecidableEq I] (S : Finset ((i : I) × B i)) :
    S ⊆ fullSites I B (S.image Sigma.fst) := by
  intro p hp
  rw [fullSites, Finset.mem_sigma]
  exact ⟨Finset.mem_image_of_mem Sigma.fst hp, Finset.mem_univ _⟩

omit [(i : I) → DecidableEq (B i)] in
/-- The site set over a set of blocks contains every site of its blocks. -/
theorem fullSites_saturated [DecidableEq I] (J : Finset I) (p : (i : I) × B i)
    (hp : p.1 ∈ (fullSites I B J).image Sigma.fst) : p ∈ fullSites I B J := by
  obtain ⟨q, hq, hqp⟩ := Finset.mem_image.1 hp
  rw [fullSites, Finset.mem_sigma] at hq ⊢
  refine ⟨?_, Finset.mem_univ _⟩
  rw [← hqp]
  exact hq.1

section Window

variable [DecidableEq I]

/-- The window of a finite site set, mapped into the free product of the
elementary abelian `2`-groups of its blocks. -/
def windowMap (S : Finset ((i : I) × B i)) :
    ↥(window I B S) →* Monoid.CoprodI (SignGroup (WFam I B (S.image Sigma.fst))) :=
  (windowFreeHom I B (S.image Sigma.fst)).comp (window I B S).subtype

/-- The kernel of `windowMap` lies in `{1, ζ}`, so it is finite. -/
theorem finite_ker_windowMap (S : Finset ((i : I) × B i)) :
    Finite (windowMap I B S).ker := by
  have hsub : ∀ k : (windowMap I B S).ker,
      ((k : window I B S) : BlockClifford I B) = 1 ∨
        ((k : window I B S) : BlockClifford I B) = sign I B := by
    intro k
    have h1 : windowFreeHom I B (S.image Sigma.fst)
        ((k : window I B S) : BlockClifford I B) = 1 :=
      MonoidHom.mem_ker.1 k.2
    have h3 : ((k : window I B S) : BlockClifford I B) ∈
        Subgroup.zpowers (sign I B) := by
      have hq := windowFromFree_windowFreeHom I B S
        ((k : window I B S) : BlockClifford I B) (k : window I B S).2
      rw [h1, map_one, QuotientGroup.mk'_apply] at hq
      exact (QuotientGroup.eq_one_iff _).mp hq.symm
    exact eq_one_or_eq_of_mem_zpowers_sq (sign_sq I B) h3
  have hmem : ∀ k : (windowMap I B S).ker,
      ((k : window I B S) : BlockClifford I B) ∈
        ({1, sign I B} : Set (BlockClifford I B)) := by
    intro k
    rcases hsub k with h | h
    · exact Set.mem_insert_iff.2 (Or.inl h)
    · exact Set.mem_insert_iff.2 (Or.inr (Set.mem_singleton_iff.2 h))
  refine Finite.of_injective
    (fun k : (windowMap I B S).ker =>
      (⟨((k : window I B S) : BlockClifford I B), hmem k⟩ :
        ({1, sign I B} : Set (BlockClifford I B)))) ?_
  intro k k' h
  exact Subtype.ext (Subtype.ext (congrArg Subtype.val h))

/-- If `S` contains every site of each of its blocks, `windowMap` is onto:
the lamps hit the coordinate flips, which generate each factor. -/
theorem windowMap_surjective (S : Finset ((i : I) × B i))
    (hS : ∀ p : (i : I) × B i, p.1 ∈ S.image Sigma.fst → p ∈ S) :
    Function.Surjective (windowMap I B S) := by
  have hflip : ∀ (j : WBlock I (S.image Sigma.fst)) (b : B j.1),
      Monoid.CoprodI.of (M := SignGroup (WFam I B (S.image Sigma.fst))) (i := j)
        (coordFlip I B j.1 b) ∈ (windowMap I B S).range := by
    intro j b
    refine MonoidHom.mem_range.2
      ⟨⟨lamp I B ⟨j.1, b⟩, lamp_mem_window I B (hS ⟨j.1, b⟩ j.2)⟩, ?_⟩
    show windowFreeHom I B (S.image Sigma.fst) (lamp I B ⟨j.1, b⟩) = _
    exact (windowFreeHom_lamp I B _ _).trans (windowFreeLamp_pos I B j.2 b)
  refine MonoidHom.range_eq_top.1 ((Subgroup.eq_top_iff' _).2 fun x => ?_)
  refine Monoid.CoprodI.induction_on (motive := fun y => y ∈ (windowMap I B S).range)
    x (one_mem _) (fun j v => ?_) (fun _ _ hx hy => mul_mem hx hy)
  have hv : v ∈ (windowMap I B S).range.comap
      (Monoid.CoprodI.of (M := SignGroup (WFam I B (S.image Sigma.fst))) (i := j)) := by
    rw [← Finset.univ_prod_mulSingle v]
    refine Subgroup.prod_mem _ fun b _ => ?_
    rcases (show ∀ x : ZMod 2, x = 0 ∨ x = 1 by decide) (Multiplicative.toAdd (v b))
      with h | h
    · rw [toAdd_eq_zero.1 h, Pi.mulSingle_one]
      exact one_mem _
    · have hv1 : v b = Multiplicative.ofAdd 1 :=
        (ofAdd_toAdd (v b)).symm.trans (congrArg Multiplicative.ofAdd h)
      have hb : Pi.mulSingle b (v b) = coordFlip I B j.1 b := by
        rw [hv1]
        funext b'
        by_cases hbb : b' = b
        · rw [hbb, Pi.mulSingle_eq_same,
            show coordFlip I B j.1 b b = Multiplicative.ofAdd 1 from if_pos rfl]
        · rw [Pi.mulSingle_eq_of_ne hbb,
            show coordFlip I B j.1 b b' = 1 from if_neg hbb]
      rw [hb]
      exact Subgroup.mem_comap.2 (hflip j b)
  exact Subgroup.mem_comap.1 hv

end Window

/-- A window over all sites of finitely many blocks has property A
(tex `sec:Esofic`, "Exactness.": Dykema for `Q_n`, then the finite `⟨ζ⟩`). -/
theorem hasPropertyA_window (J : Finset I) :
    ExactnessPermanence.HasPropertyA (window I B (fullSites I B J)) := by
  classical
  exact PropertyAFiniteKernel.hasPropertyA_of_finite_ker
    (windowMap I B (fullSites I B J))
    (windowMap_surjective I B _ (fullSites_saturated I B J))
    (finite_ker_windowMap I B _) hasPropertyA_coprodI

/-- **`C(𝒢)` has property A** (tex `sec:Esofic`, "Exactness.": the increasing
union of the windows, each exact by Dykema and the finite `⟨ζ⟩`). -/
theorem hasPropertyA_blockClifford :
    ExactnessPermanence.HasPropertyA (BlockClifford I B) := by
  classical
  refine PropertyALocality.hasPropertyA_of_directed ⟨(∅ : Finset I)⟩
    (K := fun J : Finset I => window I B (fullSites I B J)) ?_ ?_
    (hasPropertyA_window I B)
  · intro J J'
    exact ⟨J ∪ J', window_mono I B (fullSites_mono I B Finset.subset_union_left),
      window_mono I B (fullSites_mono I B Finset.subset_union_right)⟩
  · intro g
    obtain ⟨S, hS⟩ := exists_window I B g
    exact ⟨S.image Sigma.fst, window_mono I B (subset_fullSites I B S) hS⟩

end BlockClifford

/-- The literal lamp factor `C(𝒢)` of the manuscript's group has property A. -/
theorem hasPropertyA_lampFactor :
    ExactnessPermanence.HasPropertyA LiteralBlockNormalForm.LampFactor :=
  ExactnessPermanence.HasPropertyA.of_mulEquiv LiteralSoficAssembly.lampEquiv.symm
    (hasPropertyA_blockClifford LiteralBlockNormalForm.Block
      LiteralSoficAssembly.BlockSites)

#audit_axioms GroupApproximation.Full.NN09.hasPropertyA_blockClifford
#audit_closed_axioms GroupApproximation.Full.NN09.hasPropertyA_lampFactor

end GroupApproximation.Full.NN09
