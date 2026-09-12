import GroupApproximation.CharClass.LIXKRelativeMV
import GroupApproximation.CharClass.LIXKCount
import GroupApproximation.CharClass.RelativeFunctorial
import GroupApproximation.Meta.AxiomGuard

/-!
# `LocalSplit` from relative Mayer–Vietoris, at every finite set of punctures

Lane `lix-oddside` (successor of `sp-oddside`) of the stronger Problem LIX program
(`notes/LIX_STRONGER_PROGRAM_2026-09-10.md` §1.3.4).

`CharClass/LIXKRelativeMV.lean` splits a relative COCYCLE of `(X, U ∩ V)` into a cocycle of
`(X, U)` plus a cocycle of `(X, V)` whenever the open sets `U, V` cover `X`.  This file lifts
that to CLASSES and then, by induction on the number of punctures, proves the obligation
`LocalSplit` of `CharClass/LIXKCount.lean`:

```text
  for distinct points z₀, …, z_{k-1} of a T₁ space X and C = X ∖ {z₀, …, z_{k-1}},
  every x ∈ Hⁿ(X, C) is  ∑ᵢ ρᵢ(xᵢ),  where ρᵢ : Hⁿ(X, X ∖ {zᵢ}) ⟶ Hⁿ(X, C)
  is the relative pullback along the identity.
```

## The route

* **Classes.**  A relative cocycle has a class (`relCocycleClass`), every class is one
  (`relCocycleClass_surjective`), the class is additive (`relCocycleClass_add`), and pulling
  back along the identity of `X` to a smaller subspace keeps the cocycle and only enlarges the
  set it vanishes on (`relPullback_id_relCocycleClass`).
* **Two sets.**  With `C ⊆ U`, `C ⊆ V` and `U ∩ V ⊆ C`, a cocycle representing `x` vanishes on
  the `(U ∩ V)`-simplices.  The cochain split gives `α + β`, and `x = ρ_U [α] + ρ_V [β]`
  (`exists_relClass_split_of_acyclic`).
* **Punctures.**  Remove `z₀` as the second open set `X ∖ {z₀}` and the other points as the first,
  `X ∖ {z₁, …, z_{k-1}}`.  The two cover `X` because the points are distinct.  Their intersection
  is `C`.  Composites of pullbacks along the identity are pullbacks along the identity
  (`relPullback_id_comp_apply`), so the induction hands back exactly the `ρᵢ` of the statement
  (`exists_localSplit_of_acyclic`).

The only geometric input is the acyclicity of the small-annihilator complex of a two-set cover,
which the generic theorem takes as a hypothesis.  At mod-2 coefficients it is
`CupVanishSmallAnn.exists_smallAnn_preimage`, so `exists_localSplit_two` is unconditional.

## Main declarations

* `relCocycleClass`, `relCocycleClass_surjective`, `relCocycleClass_add`,
  `relPullback_id_relCocycleClass` — the relative cocycle-class API.
* `exists_relClass_split_of_acyclic` — the two-set split on classes.
* `exists_localSplit_of_acyclic` — the finite-puncture split, generic in `[CommRing R]`.
* `exists_localSplit_two` — **the same at mod-2 coefficients, in the `LocalSplit` shape.**
-/

noncomputable section

namespace GroupApproximation.CharClass

namespace LIXKRelMV

open CategoryTheory Limits AlgebraicTopology TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AffineBarycentricSubdivision

set_option linter.unusedSectionVars false

variable {R : Type} [CommRing R] {X : TopCat.{0}}

/-! ## 1. The relative cocycle class -/

/-- A cochain with vanishing coboundary is a cycle of the relative complex. -/
theorem relCochainComplex_d_hom_eq_zero {A : Set X} {n : ℕ}
    (w : relCochainSubmodule R X A n)
    (hw : cochainCoboundary R X n (w : singularCochainGroup R X n) = 0) :
    ((relCochainComplex R X A).d n (n + 1)).hom w = 0 := by
  rw [relCochainComplex_d]
  exact Subtype.ext hw

/-- The cycle of a relative cocycle, as an element of the cycles object. -/
def relCycleOf (A : Set X) (n : ℕ) (w : relCochainSubmodule R X A n)
    (hw : cochainCoboundary R X n (w : singularCochainGroup R X n) = 0) :
    (relCochainComplex R X A).cycles n :=
  (relCochainComplex R X A).cyclesMk w (n + 1) (ComplexShape.next_eq' _ rfl)
    (relCochainComplex_d_hom_eq_zero w hw)

theorem iCycles_relCycleOf (A : Set X) (n : ℕ) (w : relCochainSubmodule R X A n)
    (hw : cochainCoboundary R X n (w : singularCochainGroup R X n) = 0) :
    ((relCochainComplex R X A).iCycles n).hom (relCycleOf A n w hw) = w :=
  (relCochainComplex R X A).i_cyclesMk _ _ _ _

/-- **The class of a relative cocycle** in `Hⁿ(X, A; R)`. -/
def relCocycleClass (R : Type) [CommRing R] (X : TopCat.{0}) (A : Set X) (n : ℕ)
    (w : relCochainSubmodule R X A n)
    (hw : cochainCoboundary R X n (w : singularCochainGroup R X n) = 0) :
    relCohomology R X A n :=
  ((relCochainComplex R X A).homologyπ n).hom (relCycleOf A n w hw)

/-- The class depends only on the cochain. -/
theorem relCocycleClass_congr (A : Set X) (n : ℕ) {w w' : relCochainSubmodule R X A n}
    (h : w = w') (hw : cochainCoboundary R X n (w : singularCochainGroup R X n) = 0)
    (hw' : cochainCoboundary R X n (w' : singularCochainGroup R X n) = 0) :
    relCocycleClass R X A n w hw = relCocycleClass R X A n w' hw' := by
  subst h
  rfl

theorem relCycleOf_add (A : Set X) (n : ℕ) (w₁ w₂ : relCochainSubmodule R X A n)
    (h₁ : cochainCoboundary R X n (w₁ : singularCochainGroup R X n) = 0)
    (h₂ : cochainCoboundary R X n (w₂ : singularCochainGroup R X n) = 0)
    (h₁₂ : cochainCoboundary R X n
      ((w₁ + w₂ : relCochainSubmodule R X A n) : singularCochainGroup R X n) = 0) :
    relCycleOf A n (w₁ + w₂) h₁₂ = relCycleOf A n w₁ h₁ + relCycleOf A n w₂ h₂ := by
  apply (ModuleCat.mono_iff_injective ((relCochainComplex R X A).iCycles n)).1 inferInstance
  exact (iCycles_relCycleOf A n _ h₁₂).trans
    ((congrArg₂ (· + ·) (iCycles_relCycleOf A n w₁ h₁) (iCycles_relCycleOf A n w₂ h₂)).symm.trans
      (map_add ((relCochainComplex R X A).iCycles n).hom _ _).symm)

theorem relCycleOf_zero (A : Set X) (n : ℕ)
    (h0 : cochainCoboundary R X n
      ((0 : relCochainSubmodule R X A n) : singularCochainGroup R X n) = 0) :
    relCycleOf A n (0 : relCochainSubmodule R X A n) h0 = 0 := by
  apply (ModuleCat.mono_iff_injective ((relCochainComplex R X A).iCycles n)).1 inferInstance
  exact (iCycles_relCycleOf A n _ h0).trans
    (map_zero ((relCochainComplex R X A).iCycles n).hom).symm

/-- **The class is additive.** -/
theorem relCocycleClass_add (A : Set X) (n : ℕ) (w₁ w₂ : relCochainSubmodule R X A n)
    (h₁ : cochainCoboundary R X n (w₁ : singularCochainGroup R X n) = 0)
    (h₂ : cochainCoboundary R X n (w₂ : singularCochainGroup R X n) = 0)
    (h₁₂ : cochainCoboundary R X n
      ((w₁ + w₂ : relCochainSubmodule R X A n) : singularCochainGroup R X n) = 0) :
    relCocycleClass R X A n (w₁ + w₂) h₁₂
      = relCocycleClass R X A n w₁ h₁ + relCocycleClass R X A n w₂ h₂ := by
  unfold relCocycleClass
  rw [relCycleOf_add A n w₁ w₂ h₁ h₂ h₁₂, map_add]

/-- **Every relative class is the class of a relative cocycle.** -/
theorem relCocycleClass_surjective (A : Set X) (n : ℕ) (a : relCohomology R X A n) :
    ∃ (w : relCochainSubmodule R X A n)
      (hw : cochainCoboundary R X n (w : singularCochainGroup R X n) = 0),
      relCocycleClass R X A n w hw = a := by
  have hepi : Function.Surjective ((relCochainComplex R X A).homologyπ n).hom :=
    (ModuleCat.epi_iff_surjective _).1 inferInstance
  obtain ⟨c, hc⟩ := hepi a
  obtain ⟨w, hwdef⟩ : ∃ w : relCochainSubmodule R X A n,
      w = ((relCochainComplex R X A).iCycles n).hom c := ⟨_, rfl⟩
  have hcyc : ((relCochainComplex R X A).d n (n + 1)).hom w = 0 := by
    rw [hwdef, ← ModuleCat.comp_apply, (relCochainComplex R X A).iCycles_d n (n + 1)]
    rfl
  have hw : cochainCoboundary R X n (w : singularCochainGroup R X n) = 0 := by
    rw [relCochainComplex_d] at hcyc
    exact congrArg Subtype.val hcyc
  refine ⟨w, hw, ?_⟩
  have hmk : relCycleOf A n w hw = c := by
    apply (ModuleCat.mono_iff_injective ((relCochainComplex R X A).iCycles n)).1 inferInstance
    rw [iCycles_relCycleOf]
    exact hwdef
  unfold relCocycleClass
  rw [hmk, hc]

/-- **Pulling back along the identity keeps the cocycle.**  If `A` lies inside `B`, the
pullback `Hⁿ(X, B) ⟶ Hⁿ(X, A)` along the identity of `X` sends the class of a cocycle to the
class of the same cochain, now read as vanishing on the fewer `A`-simplices. -/
theorem relPullback_id_relCocycleClass {A B : Set X}
    (h : ∀ x ∈ A, (ConcreteCategory.hom (𝟙 X)) x ∈ B) (n : ℕ)
    (w : relCochainSubmodule R X B n)
    (hw : cochainCoboundary R X n (w : singularCochainGroup R X n) = 0)
    (hmem : (w : singularCochainGroup R X n) ∈ relCochainSubmodule R X A n) :
    (relPullback R (𝟙 X) h n).hom (relCocycleClass R X B n w hw)
      = relCocycleClass R X A n ⟨(w : singularCochainGroup R X n), hmem⟩ hw := by
  have hnat := HomologicalComplex.homologyπ_naturality (relCochainMap R (𝟙 X) h) n
  have hmk : (HomologicalComplex.cyclesMap (relCochainMap R (𝟙 X) h) n).hom
        (relCycleOf B n w hw)
      = relCycleOf A n ⟨(w : singularCochainGroup R X n), hmem⟩ hw := by
    apply (ModuleCat.mono_iff_injective ((relCochainComplex R X A).iCycles n)).1 inferInstance
    rw [iCycles_relCycleOf, ← ModuleCat.comp_apply, HomologicalComplex.cyclesMap_i,
      ModuleCat.comp_apply, iCycles_relCycleOf, relCochainMap_f_val]
    exact Subtype.ext (cochainPullback_id R X n _)
  unfold relCocycleClass
  rw [relPullback, ← ModuleCat.comp_apply, hnat, ModuleCat.comp_apply, hmk]

/-- A relative class of `(X, C)` with every point in `C` is zero: every simplex is subordinate
to `C`, so the only relative cochain is `0`. -/
theorem relCohomology_eq_zero_of_forall_mem {C : Set X} (hC : ∀ y, y ∈ C) (n : ℕ)
    (x : relCohomology R X C n) : x = 0 := by
  obtain ⟨w, hw, rfl⟩ := relCocycleClass_surjective C n x
  have hw0 : w = 0 := by
    apply Subtype.ext
    apply cochain_ext
    intro σ
    rw [w.2 σ (fun y _ => hC y)]
    exact (cochainEval_zero n σ).symm
  subst hw0
  unfold relCocycleClass
  rw [relCycleOf_zero C n hw, map_zero]

/-! ## 2. The two-set split, on classes -/

/-- Shrinking the subspace enlarges the relative cochains. -/
theorem relCochainSubmodule_le_of_subset {A B : Set X} (hAB : A ⊆ B) (n : ℕ) :
    relCochainSubmodule R X B n ≤ relCochainSubmodule R X A n :=
  fun _ hφ σ hσ => hφ σ (hσ.mono hAB)

/-- **Relative Mayer–Vietoris on classes, surjectivity half**, over an abstract acyclicity
input.  If the opens `U, V` cover `X` and `C` is their intersection (as `C ⊆ U`, `C ⊆ V`,
`U ∩ V ⊆ C`), every class of `(X, C)` is `ρ_U a + ρ_V b`. -/
theorem exists_relClass_split_of_acyclic (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ)
    (hacyclic : ∀ w : smallAnnSubmodule R X (twoSetCover U V hUV) (n + 1),
      (smallAnnD R X (twoSetCover U V hUV) (n + 1)).hom w = 0 →
      ∃ z : smallAnnSubmodule R X (twoSetCover U V hUV) n,
        (smallAnnD R X (twoSetCover U V hUV) n).hom z = w)
    {C : Set X} (hCU : C ⊆ (U : Set X)) (hCV : C ⊆ (V : Set X))
    (hUVC : (U : Set X) ∩ (V : Set X) ⊆ C) (x : relCohomology R X C n) :
    ∃ (a : relCohomology R X (U : Set X) n) (b : relCohomology R X (V : Set X) n),
      x = (relPullback R (𝟙 X) (fun _ hy => hCU hy) n).hom a
        + (relPullback R (𝟙 X) (fun _ hy => hCV hy) n).hom b := by
  obtain ⟨w, hw, rfl⟩ := relCocycleClass_surjective C n x
  have hφ : (w : singularCochainGroup R X n)
      ∈ relCochainSubmodule R X ((U : Set X) ∩ (V : Set X)) n :=
    relCochainSubmodule_le_of_subset hUVC n w.2
  obtain ⟨α, β, hα, hβ, hδα, hδβ, hsum⟩ :=
    exists_relCocycle_split_of_acyclic U V hUV n hacyclic hφ hw
  refine ⟨relCocycleClass R X (U : Set X) n ⟨α, hα⟩ hδα,
    relCocycleClass R X (V : Set X) n ⟨β, hβ⟩ hδβ, ?_⟩
  rw [relPullback_id_relCocycleClass (fun _ hy => hCU hy) n ⟨α, hα⟩ hδα
      (relCochainSubmodule_le_of_subset hCU n hα),
    relPullback_id_relCocycleClass (fun _ hy => hCV hy) n ⟨β, hβ⟩ hδβ
      (relCochainSubmodule_le_of_subset hCV n hβ)]
  have hδ : cochainCoboundary R X n
      (((⟨α, relCochainSubmodule_le_of_subset hCU n hα⟩ : relCochainSubmodule R X C n)
        + ⟨β, relCochainSubmodule_le_of_subset hCV n hβ⟩ : relCochainSubmodule R X C n) :
          singularCochainGroup R X n) = 0 := by
    show cochainCoboundary R X n (α + β) = 0
    rw [hsum]
    exact hw
  rw [← relCocycleClass_add C n ⟨α, relCochainSubmodule_le_of_subset hCU n hα⟩
    ⟨β, relCochainSubmodule_le_of_subset hCV n hβ⟩ hδα hδβ hδ]
  have hw' : w = (⟨α, relCochainSubmodule_le_of_subset hCU n hα⟩ : relCochainSubmodule R X C n)
      + ⟨β, relCochainSubmodule_le_of_subset hCV n hβ⟩ := Subtype.ext hsum.symm
  exact relCocycleClass_congr C n hw' hw hδ

/-! ## 3. Finitely many punctures -/

/-- The identity of `X` is a map of pairs from `(X, C)` to `(X, X ∖ {zᵢ})` whenever `C` avoids
every `zᵢ`. -/
theorem mapsTo_compl_puncture {k : ℕ} {z : Fin k → X} {C : Set X}
    (hC : ∀ y, y ∈ C ↔ ∀ i, y ≠ z i) (i : Fin k) :
    ∀ y ∈ C, (ConcreteCategory.hom (𝟙 X)) y ∈ ({z i}ᶜ : Set X) :=
  fun y hy => (hC y).1 hy i

/-- Composites of pullbacks along the identity are the pullback along the identity. -/
theorem relPullback_id_comp_apply {A B D : Set X}
    (hAB : ∀ y ∈ A, (ConcreteCategory.hom (𝟙 X)) y ∈ B)
    (hBD : ∀ y ∈ B, (ConcreteCategory.hom (𝟙 X)) y ∈ D)
    (hAD : ∀ y ∈ A, (ConcreteCategory.hom (𝟙 X)) y ∈ D) (n : ℕ)
    (v : relCohomology R X D n) :
    (relPullback R (𝟙 X) hAB n).hom ((relPullback R (𝟙 X) hBD n).hom v)
      = (relPullback R (𝟙 X) hAD n).hom v := by
  have hfg : ∀ y ∈ A, (ConcreteCategory.hom (𝟙 X ≫ 𝟙 X)) y ∈ D := by
    intro y hy
    rw [Category.comp_id]
    exact hAD y hy
  have h := relPullback_comp R (𝟙 X) (𝟙 X) hAB hBD hfg n
  rw [relPullback_eq_of_eq R (Category.comp_id (𝟙 X)) hfg n] at h
  rw [← ModuleCat.comp_apply, ← h]

/-- **The finite-puncture split, over an abstract acyclicity input.**  For distinct points
`z₀, …, z_{k-1}` of a T₁ space and `C` their complement, every class of `(X, C)` is the sum of
the images of `k` classes, one on each single-puncture pair, under the pullbacks along the
identity. -/
theorem exists_localSplit_of_acyclic [T1Space X] (n : ℕ)
    (hacyclic : ∀ (U V : Opens X) (hUV : U ⊔ V = ⊤)
      (w : smallAnnSubmodule R X (twoSetCover U V hUV) (n + 1)),
      (smallAnnD R X (twoSetCover U V hUV) (n + 1)).hom w = 0 →
      ∃ z : smallAnnSubmodule R X (twoSetCover U V hUV) n,
        (smallAnnD R X (twoSetCover U V hUV) n).hom z = w) :
    ∀ (k : ℕ) (z : Fin k → X), Function.Injective z →
      ∀ (C : Set X) (hC : ∀ y, y ∈ C ↔ ∀ i, y ≠ z i) (x : relCohomology R X C n),
        ∃ xloc : ∀ i, relCohomology R X ({z i}ᶜ : Set X) n,
          x = ∑ i, (relPullback R (𝟙 X) (mapsTo_compl_puncture hC i) n).hom (xloc i) := by
  intro k
  induction k with
  | zero =>
    intro z _ C hC x
    refine ⟨fun i => Fin.elim0 i, ?_⟩
    rw [Fin.sum_univ_zero]
    exact relCohomology_eq_zero_of_forall_mem (fun y => (hC y).2 fun i => Fin.elim0 i) n x
  | succ k ih =>
    intro z hz C hC x
    have hUopen : IsOpen {y : X | ∀ i : Fin k, y ≠ z i.succ} := by
      rw [Set.setOf_forall]
      exact isOpen_iInter_of_finite fun _ => isOpen_ne
    have hVopen : IsOpen ({z 0}ᶜ : Set X) := isClosed_singleton.isOpen_compl
    have hUV : (⟨{y : X | ∀ i : Fin k, y ≠ z i.succ}, hUopen⟩ : Opens X)
        ⊔ ⟨({z 0}ᶜ : Set X), hVopen⟩ = ⊤ := by
      refine TopologicalSpace.Opens.ext ?_
      rw [TopologicalSpace.Opens.coe_sup, TopologicalSpace.Opens.coe_top]
      refine Set.eq_univ_of_forall fun y => ?_
      rw [Set.mem_union]
      by_cases hy : y = z 0
      · exact Or.inl fun i hi => Fin.succ_ne_zero i (hz (hi.symm.trans hy))
      · exact Or.inr hy
    have hCU : C ⊆ ((⟨{y : X | ∀ i : Fin k, y ≠ z i.succ}, hUopen⟩ : Opens X) : Set X) :=
      fun y hy i => (hC y).1 hy i.succ
    have hCV : C ⊆ ((⟨({z 0}ᶜ : Set X), hVopen⟩ : Opens X) : Set X) :=
      fun y hy => (hC y).1 hy 0
    have hUVC : ((⟨{y : X | ∀ i : Fin k, y ≠ z i.succ}, hUopen⟩ : Opens X) : Set X)
        ∩ ((⟨({z 0}ᶜ : Set X), hVopen⟩ : Opens X) : Set X) ⊆ C := by
      intro y hy
      refine (hC y).2 fun i => ?_
      cases i using Fin.cases with
      | zero => exact hy.2
      | succ j => exact hy.1 j
    obtain ⟨a, b, hab⟩ := exists_relClass_split_of_acyclic _ _ hUV n (hacyclic _ _ hUV)
      hCU hCV hUVC x
    obtain ⟨aloc, ha⟩ := ih (fun i => z i.succ) (fun i j hij => Fin.succ_inj.mp (hz hij))
      {y : X | ∀ i : Fin k, y ≠ z i.succ} (fun _ => Iff.rfl) a
    refine ⟨fun i => Fin.cases (motive := fun i => relCohomology R X ({z i}ᶜ : Set X) n)
      b aloc i, ?_⟩
    rw [hab, ha, map_sum, Fin.sum_univ_succ]
    refine (add_comm _ _).trans (congrArg₂ (· + ·) rfl (Finset.sum_congr rfl fun i _ => ?_))
    exact relPullback_id_comp_apply _ _ _ n (aloc i)

/-- **The finite-puncture split at mod-2 coefficients, unconditionally**, in the shape of
`CharClass/LIXKCount.lean`'s `LocalSplit`.  The acyclicity input is
`CupVanishSmallAnn.exists_smallAnn_preimage`. -/
theorem exists_localSplit_two {X : TopCat.{0}} [T1Space X] {k : ℕ} (z : Fin k → X)
    (hz : Function.Injective z) {C : Set X} (hC : ∀ y, y ∈ C ↔ ∀ i, y ≠ z i) (n : ℕ)
    (x : relCohomology (ZMod 2) X C n) :
    ∃ xloc : ∀ i, relCohomology (ZMod 2) X ({z i}ᶜ : Set X) n,
      LocalSplit (fun i => relPullback (ZMod 2) (𝟙 X) (mapsTo_compl_puncture hC i) n)
        x xloc :=
  exists_localSplit_of_acyclic n
    (fun U V hUV w hw => exists_smallAnn_preimage X (twoSetCover U V hUV) n w hw)
    k z hz C hC x

end LIXKRelMV

/-! Audited on every build. -/

#audit_axioms LIXKRelMV.relCocycleClass_surjective
#audit_axioms LIXKRelMV.relPullback_id_relCocycleClass
#audit_axioms LIXKRelMV.exists_relClass_split_of_acyclic
#audit_axioms LIXKRelMV.exists_localSplit_of_acyclic
#audit_axioms LIXKRelMV.exists_localSplit_two

end GroupApproximation.CharClass
