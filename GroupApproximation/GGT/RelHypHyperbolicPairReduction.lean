import GroupApproximation.GGT.RelHypSuitabilityClosure

/-!
# The exact geometric leaf for a non-commensurable hyperbolic pair

The manuscript only needs two infinite-order elements in distinct Osin
commensurability classes.  This file removes all bookkeeping from that request.

The remaining input below is the standard fixed-axis form of the hyperbolic
group theorem: in a non-elementary hyperbolic group, every loxodromic element
has a loxodromic element outside its ambient commensurability class.  This is
the conjugator-sensitive conclusion; geometric independence alone is weaker
and cannot replace it.

Everything around that geometric assertion is proved here.  In particular,
non-elementarity supplies a nontrivial element, torsion-freeness makes it
infinite-order, and the finite hyperbolic Cayley graph makes it loxodromic.
Thus this is a one-leaf reduction of
`HyperbolicNonCommensurablePairStatement`, with no separate existence,
infinite-order, alphabet, or transport assumptions.
-/

namespace GroupApproximation
namespace GGT
namespace RelHyp

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

/-- **The fixed-axis commensurability-avoidance theorem for hyperbolic groups.**

This is the precise remaining geometric theorem.  It is stronger than the
manuscript consumer in two useful ways: the first loxodromic is prescribed,
and the returned second element is itself loxodromic. -/
def HyperbolicLoxodromicCommensurabilityEscape : Prop :=
  ∀ (H : Type) (_ : Group H) (A : Alphabet H), A.carrier.Finite →
    ∀ δ : ℝ, IsHyperbolicSpace δ (Cayley A) →
      ¬ IsElementaryGroup H →
        ∀ g : H, IsLoxodromic g (Cayley.base A) →
          ∃ h : H, IsLoxodromic h (Cayley.base A) ∧
            ¬ OsinCommensurable g h

/-- A non-elementary group is nontrivial.  The contrapositive is elementary:
in a subsingleton group the top subgroup is cyclic and has index one. -/
theorem nontrivial_of_not_isElementaryGroup {H : Type} [Group H]
    (hne : ¬ IsElementaryGroup H) : Nontrivial H := by
  by_contra hnt
  haveI : Subsingleton H := not_nontrivial_iff_subsingleton.mp hnt
  apply hne
  exact ⟨⊤, inferInstance, inferInstance⟩

/-- The fixed-axis theorem is the only missing input for the manuscript's
non-commensurable-pair statement. -/
theorem hyperbolicNonCommensurablePairStatement_of_escape
    (hescape : HyperbolicLoxodromicCommensurabilityEscape) :
    HyperbolicNonCommensurablePairStatement := by
  intro H instH hne htf
  letI := instH
  haveI : Nontrivial H := nontrivial_of_not_isElementaryGroup hne.2
  obtain ⟨g, hg1⟩ := exists_ne (1 : H)
  obtain ⟨T, hT, δ, hδ⟩ := hne.1
  let A : Alphabet H := ⟨(T : Set H), hT⟩
  have hAfin : A.carrier.Finite := T.finite_toSet
  have hAδ : IsHyperbolicSpace (δ : ℝ) (Cayley A) :=
    isHyperbolicSpace_cayley_of_fourPoint A hδ
  have hglox : IsLoxodromic g (Cayley.base A) :=
    HullSCUnionGeometry.isLoxodromic_cayley_of_not_isOfFinOrder
      A hAfin hAδ (htf.not_isOfFinOrder hg1)
  obtain ⟨h, hhlox, hnc⟩ :=
    hescape H instH A hAfin (δ : ℝ) hAδ hne.2 g hglox
  refine ⟨g, h, ?_, ?_, hnc⟩
  · intro n hn hpow
    exact not_isOfFinOrder_of_isLoxodromic hglox
      (isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, hpow⟩)
  · intro n hn hpow
    exact not_isOfFinOrder_of_isLoxodromic hhlox
      (isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, hpow⟩)

end RelHyp
end GGT
end GroupApproximation
