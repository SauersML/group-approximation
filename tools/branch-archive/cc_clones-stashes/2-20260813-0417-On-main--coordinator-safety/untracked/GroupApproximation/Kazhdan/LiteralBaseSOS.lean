import GroupApproximation.Kazhdan.GroupRingSOSPropertyT
import GroupApproximation.Kazhdan.RationalGroupRingCertificate
import GroupApproximation.Sofic.LiteralNonMFPresentation

/-!
# An exact SOS target for the literal six-generator base

This file specializes the general group-ring sum-of-squares criterion to the
literal base presentation printed in the manuscript.  It removes presentation
and generating-set bookkeeping from the remaining mathematical task: an exact
finite group-ring identity for `baseControlSet` now implies property `(T)` of
the literal base directly.

No numerical solver output and no unverified positivity assertion enters this
module.  The certificate proposition below requires an exact equality in the
real group ring.
-/

namespace GroupApproximation
namespace LiteralBaseSOS

open LiteralNonMFPresentation

noncomputable section

local instance : DecidableEq Base := Classical.decEq Base

/-- The six distinguished generators of the literal base presentation. -/
def baseLetters : Finset Base :=
  Finset.univ.image PresentedGroup.of

/-- The symmetric twelve-letter control set consisting of the six printed
generators and their inverses.  Coincidences in the presented group are
automatically removed by `Finset`. -/
def baseControlSet : Finset Base :=
  baseLetters ∪ baseLetters.image (fun g ↦ g⁻¹)

theorem mem_baseControlSet_iff (g : Base) :
    g ∈ baseControlSet ↔
      ∃ i : BaseGenerator,
        g = PresentedGroup.of i ∨ g = (PresentedGroup.of i)⁻¹ := by
  classical
  simp [baseControlSet, baseLetters, eq_comm]
  constructor
  · rintro (⟨i, hi⟩ | ⟨i, hi⟩)
    · exact ⟨i, Or.inl hi⟩
    · exact ⟨i, Or.inr hi⟩
  · rintro ⟨i, hi | hi⟩
    · exact Or.inl ⟨i, hi⟩
    · exact Or.inr ⟨i, hi⟩

/-- The literal control set is closed under inversion. -/
theorem baseControlSet_inv_closed (g : Base) :
    g ∈ baseControlSet ↔ g⁻¹ ∈ baseControlSet := by
  have hforward : ∀ h : Base,
      h ∈ baseControlSet → h⁻¹ ∈ baseControlSet := by
    intro h hh
    rw [mem_baseControlSet_iff] at hh ⊢
    rcases hh with ⟨i, rfl | rfl⟩
    · exact ⟨i, Or.inr rfl⟩
    · exact ⟨i, Or.inl (by simp)⟩
  constructor
  · exact hforward g
  · intro hg
    simpa using hforward g⁻¹ hg

/-- The symmetric control set generates the literal presented base. -/
theorem closure_baseControlSet :
    Subgroup.closure (baseControlSet : Set Base) = ⊤ := by
  apply top_unique
  intro g _hg
  apply PresentedGroup.generated_by
    ((baseRelators : Finset (FreeGroup BaseGenerator)) :
      Set (FreeGroup BaseGenerator))
    (Subgroup.closure (baseControlSet : Set Base)) ?_ g
  intro i
  apply Subgroup.subset_closure
  change PresentedGroup.of i ∈ baseControlSet
  rw [mem_baseControlSet_iff]
  exact ⟨i, Or.inl rfl⟩

/-- Exact finite certificate data sufficient for property `(T)` of the
literal base.  The only non-structural field is the group-ring SOS identity. -/
def IsCertificate (c : ℝ) : Prop :=
  0 < c ∧
    c ≤ (2 * baseControlSet.card : ℝ) ∧
    RealGroupRing.IsSOSQuadraticGap baseControlSet c

/-- A literal-base certificate supplies every field of the generic exact
Kazhdan SOS criterion. -/
theorem isKazhdanSOSCertificate_of_isCertificate {c : ℝ}
    (hcert : IsCertificate c) :
    GroupRingSOSPropertyT.IsKazhdanSOSCertificate baseControlSet c := by
  rcases hcert with ⟨hc, hbound, hsos⟩
  exact ⟨hc, hbound, closure_baseControlSet,
    RealGroupRing.adjoint_laplacianElement_of_inv_closed
      baseControlSet baseControlSet_inv_closed,
    hsos⟩

/-- **Concrete exact target for the manuscript's remaining property `(T)`
gap.**  Any exact SOS certificate for the literal symmetric generating set
proves property `(T)` of the six-generator base, with no external property
`(T)` axiom. -/
theorem base_hasKazhdanPropertyT_of_isCertificate {c : ℝ}
    (hcert : IsCertificate c) :
    HasKazhdanPropertyT.{0, 0} Base :=
  GroupRingSOSPropertyT.hasKazhdanPropertyT_of_sosCertificate
    baseControlSet (isKazhdanSOSCertificate_of_isCertificate hcert)

/-- Rational certificate data is the preferred proof-carrying input format:
all coefficients and the group-ring identity are exact. -/
def IsRationalCertificate (c : ℚ) : Prop :=
  0 < c ∧
    (c : ℝ) ≤ (2 * baseControlSet.card : ℝ) ∧
    RationalGroupRingCertificate.IsRationalSOSQuadraticGap
      baseControlSet c

/-- An exact rational certificate closes the literal-base property `(T)` gap
after coefficientwise embedding into the real group ring. -/
theorem base_hasKazhdanPropertyT_of_isRationalCertificate {c : ℚ}
    (hcert : IsRationalCertificate c) :
    HasKazhdanPropertyT.{0, 0} Base := by
  rcases hcert with ⟨hc, hbound, hsos⟩
  apply base_hasKazhdanPropertyT_of_isCertificate (c := (c : ℝ))
  exact ⟨by exact_mod_cast hc, hbound,
    RationalGroupRingCertificate.real_sos_of_rational_sos
      baseControlSet hsos⟩

end

end LiteralBaseSOS
end GroupApproximation
