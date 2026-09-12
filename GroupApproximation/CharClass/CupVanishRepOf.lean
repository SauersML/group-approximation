import GroupApproximation.CharClass.CupVanishCover
import GroupApproximation.Meta.AxiomGuard

/-!
# The two-set cup-vanishing theorem over a field

Lane `lix-cupone`: the coefficient-generic twin of `CartanCoverRep`, `CupVanishSmallAnn` and
`CupVanishCover`, for lix-lh's odd-primary Chern layer.  The `F₂` names are unchanged and nothing
existing is edited.

If `a` restricts to zero on `U`, `b` restricts to zero on `V`, and `U ∪ V = X`, then `a ⌣ b = 0`.  The
proof is the `F₂` one with the coefficient field `K` in place of `ZMod 2`: a class vanishing on a
subspace has a representative vanishing there (the long exact sequence of the pair,
`relLES_exact_abs`, already generic), the cup of the two representatives vanishes on every simplex
small for the cover (`cochainCup_mem_smallAnn`, already generic), and a small-annihilating cocycle is
a coboundary by acyclicity of the small-annihilator complex, which over a field is
`smallAnnComplexOf_acyclic`.  `[Field K]` enters only there.

## Main declarations

* `exists_cocycle_vanishing_onOf` — the representative.
* `cocycleClassK_eq_zero_of_mem_smallAnnOf`, `…_posOf` — the small-annihilator step.
* `cup_eq_zero_of_absToSub_eq_zeroOf` — **the two-set theorem over `K`.**
-/

set_option autoImplicit false

namespace GroupApproximation.CharClass

open CategoryTheory TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

noncomputable section

/-! ## 1. A representative vanishing on the subspace -/

/-- **A class restricting to zero on `A` has a cocycle representative vanishing on every simplex
lying in `A`**, over any commutative ring. -/
theorem exists_cocycle_vanishing_onOf (K : Type) [CommRing K] (X : TopCat.{0}) (A : Set X)
    (n : ℕ) (a : Hmod K X n) (ha : (absToSub K A n).hom a = 0) :
    ∃ (φ : singularCochainGroup K X n)
      (_hmem : φ ∈ relCochainSubmodule K X A n)
      (hφ : cochainCoboundary K X n φ = 0),
      cocycleClassK K X n φ hφ = a := by
  obtain ⟨c, hc⟩ := relLES_exact_abs K X A n a ha
  have hepi : Function.Surjective ((relCochainComplex K X A).homologyπ n).hom :=
    (ModuleCat.epi_iff_surjective _).1 inferInstance
  obtain ⟨z, hz⟩ := hepi c
  set w : relCochainSubmodule K X A n := ((relCochainComplex K X A).iCycles n).hom z with hw
  have hcyc : ((relCochainComplex K X A).d n (n + 1)).hom w = 0 := by
    rw [hw, ← ModuleCat.comp_apply, (relCochainComplex K X A).iCycles_d n (n + 1)]
    rfl
  have habs : cochainCoboundary K X n (w : singularCochainGroup K X n) = 0 := by
    have h2 : ((cochainCx K X).d n (n + 1)).hom (((relInclusion K X A).f n).hom w)
        = ((relInclusion K X A).f (n + 1)).hom (((relCochainComplex K X A).d n (n + 1)).hom w) := by
      simp only [← ModuleCat.comp_apply]
      rw [(relInclusion K X A).comm n (n + 1)]
    rw [← cochainCx_d_apply]
    show ((cochainCx K X).d n (n + 1)).hom (((relInclusion K X A).f n).hom w) = 0
    rw [h2, hcyc, map_zero]
  refine ⟨(w : singularCochainGroup K X n), w.2, habs, ?_⟩
  have hnat := HomologicalComplex.homologyπ_naturality (relInclusion K X A) n
  have hnat' := congrArg (fun m => ModuleCat.Hom.hom m z) hnat
  simp only [ModuleCat.comp_apply] at hnat'
  have hmk : (cochainCx K X).cyclesMk (w : singularCochainGroup K X n) (n + 1)
        (ComplexShape.next_eq' _ rfl) habs
      = (HomologicalComplex.cyclesMap (relInclusion K X A) n).hom z := by
    apply (ModuleCat.mono_iff_injective ((cochainCx K X).iCycles n)).1 inferInstance
    refine Eq.trans ((cochainCx K X).i_cyclesMk _ _ _ _) ?_
    rw [← ModuleCat.comp_apply, HomologicalComplex.cyclesMap_i]
    rfl
  show ((cochainCx K X).homologyπ n).hom
      ((cochainCx K X).cyclesMk (w : singularCochainGroup K X n) (n + 1)
        (ComplexShape.next_eq' _ rfl) habs) = a
  rw [hmk, ← hnat', hz]
  exact hc

/-! ## 2. Small-annihilating cocycles have zero class -/

/-- **Cycles are boundaries in the small-annihilator complex**, over a field. -/
theorem exists_smallAnn_preimageOf (K : Type) [Field K] (X : TopCat.{0}) (𝒰 : OpenCoverData X)
    (n : ℕ) (w : smallAnnSubmodule K X 𝒰 (n + 1))
    (hw : (smallAnnD K X 𝒰 (n + 1)).hom w = 0) :
    ∃ z : smallAnnSubmodule K X 𝒰 n, (smallAnnD K X 𝒰 n).hom z = w := by
  have hprev : (ComplexShape.up ℕ).prev (n + 1) = n := by simp
  have hnext : (ComplexShape.up ℕ).next (n + 1) = n + 2 := by simp
  have hex : (smallAnnComplex K X 𝒰).ExactAt (n + 1) := smallAnnComplexOf_acyclic K X 𝒰 (n + 1)
  rw [HomologicalComplex.exactAt_iff' (K := smallAnnComplex K X 𝒰)
      (i := n) (j := n + 1) (k := n + 2) hprev hnext,
    ShortComplex.moduleCat_exact_iff] at hex
  have hw' : ((smallAnnComplex K X 𝒰).d (n + 1) (n + 2)).hom w = 0 := by
    rw [smallAnnComplex_d]
    exact hw
  obtain ⟨z, hz⟩ := hex w hw'
  refine ⟨z, ?_⟩
  rw [← smallAnnComplex_d]
  exact hz

/-- **A cocycle vanishing on every small simplex has zero class**, over a field. -/
theorem cocycleClassK_eq_zero_of_mem_smallAnnOf (K : Type) [Field K] (X : TopCat.{0})
    (𝒰 : OpenCoverData X) (n : ℕ) (φ : singularCochainGroup K X (n + 1))
    (hmem : φ ∈ smallAnnSubmodule K X 𝒰 (n + 1))
    (hφ : cochainCoboundary K X (n + 1) φ = 0) :
    cocycleClassK K X (n + 1) φ hφ = 0 := by
  have hd : (smallAnnD K X 𝒰 (n + 1)).hom
      (⟨φ, hmem⟩ : smallAnnSubmodule K X 𝒰 (n + 1)) = 0 := Subtype.ext hφ
  obtain ⟨z, hz⟩ := exists_smallAnn_preimageOf K X 𝒰 n ⟨φ, hmem⟩ hd
  have hz' : cochainCoboundary K X n (z : singularCochainGroup K X n) = φ :=
    congrArg Subtype.val hz
  rw [cocycleClassK_congr K X (n + 1) hz'.symm hφ
    (cochainCoboundary_cochainCoboundaryK K X n z)]
  exact cocycleClassK_coboundary_zero K X n z _

/-- The small-annihilator step at a degree only known to be positive. -/
theorem cocycleClassK_eq_zero_of_mem_smallAnn_posOf (K : Type) [Field K] (X : TopCat.{0})
    (𝒰 : OpenCoverData X) (m : ℕ) (hm : 0 < m) (φ : singularCochainGroup K X m)
    (hmem : φ ∈ smallAnnSubmodule K X 𝒰 m) (hφ : cochainCoboundary K X m φ = 0) :
    cocycleClassK K X m φ hφ = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  exact cocycleClassK_eq_zero_of_mem_smallAnnOf K X 𝒰 n φ hmem hφ

/-! ## 3. The two-set theorem -/

/-- **The two-set theorem over a field.**  If `a` restricts to zero on `U`, `b` restricts to zero
on `V`, and `U` and `V` cover, then `a ⌣ b = 0`. -/
theorem cup_eq_zero_of_absToSub_eq_zeroOf (K : Type) [Field K] {X : TopCat.{0}}
    (U V : Opens X) (hUV : U ⊔ V = ⊤) {p q : ℕ} (hpq : 0 < p + q) (a : Hmod K X p)
    (b : Hmod K X q) (ha : (absToSub K (U : Set X) p).hom a = 0)
    (hb : (absToSub K (V : Set X) q).hom b = 0) :
    cup a b = 0 := by
  obtain ⟨α, hαmem, hαc, rfl⟩ := exists_cocycle_vanishing_onOf K X (U : Set X) p a ha
  obtain ⟨β, hβmem, hβc, rfl⟩ := exists_cocycle_vanishing_onOf K X (V : Set X) q b hb
  rw [cup_mkOf]
  exact cocycleClassK_eq_zero_of_mem_smallAnn_posOf K X (twoSetCover U V hUV) (p + q) hpq
    (cochainCup p q α β) (cochainCup_mem_smallAnn U V hUV hαmem hβmem) _

/-- Over every field, a cup product of two classes vanishing on the two members of an open cover
is zero. -/
def PrintedCupVanishTwoSet : Prop :=
  ∀ (K : Type) [Field K] (X : TopCat.{0}) (U V : Opens X), U ⊔ V = ⊤ →
    ∀ (p q : ℕ), 0 < p + q → ∀ (a : Hmod K X p) (b : Hmod K X q),
      (absToSub K (U : Set X) p).hom a = 0 → (absToSub K (V : Set X) q).hom b = 0 → cup a b = 0

theorem printedCupVanishTwoSet : PrintedCupVanishTwoSet := by
  intro K _ X U V hUV p q hpq a b ha hb
  exact cup_eq_zero_of_absToSub_eq_zeroOf K U V hUV hpq a b ha hb

#audit_closed_axioms printedCupVanishTwoSet

end

end GroupApproximation.CharClass
