import GroupApproximation.CharClass.RelativeLES
import GroupApproximation.CharClass.CohomologyBasic

/-!
# A class vanishing on a subspace has a representative vanishing there

The cup-vanishing lemma for a cover needs cocycle representatives that vanish
identically on the simplices of a subspace, not merely up to a coboundary.  The
long exact sequence of the pair already says the class comes from the relative
group, and the relative cochains are by definition the ones that vanish; this
file joins the two.

Nothing here is about a cover yet.  It is stated for one subspace, so it applies
to each of `U` and `V` separately, which is how the cup-product step consumes it.

## Main results

* `exists_cocycle_vanishing_on` — **the representative**.
-/

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

/-- **A class restricting to zero on `A` has a cocycle representative vanishing
on every simplex whose image lies in `A`.** -/
theorem exists_cocycle_vanishing_on (X : TopCat.{0}) (A : Set X) (n : ℕ)
    (a : Hmod2 X n) (ha : (absToSub (ZMod 2) A n).hom a = 0) :
    ∃ (φ : singularCochainGroup (ZMod 2) X n)
      (_hmem : φ ∈ relCochainSubmodule (ZMod 2) X A n)
      (hφ : cochainCoboundary (ZMod 2) X n φ = 0),
      cocycleClass X n φ hφ = a := by
  obtain ⟨c, hc⟩ := relLES_exact_abs (ZMod 2) X A n a ha
  have hepi : Function.Surjective
      ((relCochainComplex (ZMod 2) X A).homologyπ n).hom :=
    (ModuleCat.epi_iff_surjective _).1 inferInstance
  obtain ⟨z, hz⟩ := hepi c
  set w : relCochainSubmodule (ZMod 2) X A n :=
    ((relCochainComplex (ZMod 2) X A).iCycles n).hom z with hw
  -- the relative cochain is a relative cocycle
  have hcyc : ((relCochainComplex (ZMod 2) X A).d n (n + 1)).hom w = 0 := by
    rw [hw, ← ModuleCat.comp_apply,
      (relCochainComplex (ZMod 2) X A).iCycles_d n (n + 1)]
    rfl
  -- hence its image is an absolute cocycle
  have habs : cochainCoboundary (ZMod 2) X n (w : singularCochainGroup (ZMod 2) X n)
      = 0 := by
    have h2 : ((cochainCx (ZMod 2) X).d n (n + 1)).hom
          (((relInclusion (ZMod 2) X A).f n).hom w)
        = ((relInclusion (ZMod 2) X A).f (n + 1)).hom
            (((relCochainComplex (ZMod 2) X A).d n (n + 1)).hom w) := by
      simp only [← ModuleCat.comp_apply]
      rw [(relInclusion (ZMod 2) X A).comm n (n + 1)]
    rw [← cochainCx_d_apply]
    show ((cochainCx (ZMod 2) X).d n (n + 1)).hom
      (((relInclusion (ZMod 2) X A).f n).hom w) = 0
    rw [h2, hcyc, map_zero]
  refine ⟨(w : singularCochainGroup (ZMod 2) X n), w.2, habs, ?_⟩
  -- the class is `a`
  have hnat := HomologicalComplex.homologyπ_naturality (relInclusion (ZMod 2) X A) n
  have hnat' := congrArg (fun m => ModuleCat.Hom.hom m z) hnat
  simp only [ModuleCat.comp_apply] at hnat'
  have hmk : (cochainCx (ZMod 2) X).cyclesMk
        (w : singularCochainGroup (ZMod 2) X n) (n + 1)
        (ComplexShape.next_eq' _ rfl) habs
      = (HomologicalComplex.cyclesMap (relInclusion (ZMod 2) X A) n).hom z := by
    apply (ModuleCat.mono_iff_injective ((cochainCx (ZMod 2) X).iCycles n)).1 inferInstance
    refine Eq.trans ((cochainCx (ZMod 2) X).i_cyclesMk _ _ _ _) ?_
    rw [← ModuleCat.comp_apply, HomologicalComplex.cyclesMap_i]
    rfl
  show ((cochainCx (ZMod 2) X).homologyπ n).hom
      ((cochainCx (ZMod 2) X).cyclesMk (w : singularCochainGroup (ZMod 2) X n) (n + 1)
        (ComplexShape.next_eq' _ rfl) habs) = a
  rw [hmk, ← hnat', hz]
  exact hc

end

end GroupApproximation.CharClass
