import GroupApproximation.Sofic.HyperlinearReduction
import GroupApproximation.Sofic.KazhdanCornerDiagonal
import Mathlib.GroupTheory.Subgroup.Simple

/-!
# The Kazhdan-corner reduction

This file assembles the finite-stage spectral construction from the adjacent
modules into the Kazhdan-corner theorem.  Property `(T)` supplies finite
generation and hence countability.  A diagonal sequence of nonzero moving
spectral corners then gives a nontrivial homomorphism into a tracial matrix
ultraproduct.  Its range is a nontrivial hyperlinear quotient.  If the source
group is simple, the homomorphism is injective and the source is hyperlinear.

Thus one weak-MF certificate for a simple property-`(T)` nonsofic group is a
single-certificate solution of the hyperlinear-nonsofic existence problem.
-/

namespace GroupApproximation

universe u

variable {G H : Type u} [Group G] [Group H]

/-! ## The desired quotient -/

/-- `G` has a nontrivial hyperlinear quotient.  The quotient is presented by
a surjective homomorphism rather than by choosing a particular normal
subgroup; `rangeRestrict` will provide precisely this presentation below. -/
def HasNontrivialHyperlinearQuotient (G : Type u) [Group G] : Prop :=
  ∃ (Q : Type u) (_ : Group Q) (q : G →* Q),
    Function.Surjective q ∧ IsHyperlinear Q ∧ ∃ g : G, q g ≠ 1

/-- The output of the analytic Kazhdan-corner construction: a nontrivial
homomorphism into a hyperlinear group.  Passing to its range turns this into
the quotient formulation without asking hyperlinearity to pass to arbitrary
quotients. -/
def HasHyperlinearCornerRepresentation (G : Type u) [Group G] : Prop :=
  ∃ (H : Type u) (_ : Group H), IsHyperlinear H ∧
    ∃ ρ : G →* H, ∃ g : G, ρ g ≠ 1

/-- A hyperlinear nontrivial group has a corner representation, namely its
identity representation.  Besides being useful below, this is a positive
control showing that the certificate is satisfiable. -/
theorem hasHyperlinearCornerRepresentation_of_isHyperlinear [Nontrivial G]
    (hG : IsHyperlinear G) : HasHyperlinearCornerRepresentation G := by
  obtain ⟨g, hg⟩ := exists_ne (1 : G)
  refine ⟨G, inferInstance, hG, MonoidHom.id G, g, ?_⟩
  simpa using hg

/-- Closed positive control for the corner representation certificate. -/
theorem hasHyperlinearCornerRepresentation_cyclicTwo :
    HasHyperlinearCornerRepresentation (Multiplicative (ZMod 2)) :=
  hasHyperlinearCornerRepresentation_of_isHyperlinear
    (isHyperlinear_of_finite (Multiplicative (ZMod 2)))

/-! ## The range is the quotient -/

/-- Any nontrivial homomorphism into a hyperlinear group produces a
nontrivial hyperlinear quotient: take its range. -/
theorem hasNontrivialHyperlinearQuotient_of_hom
    (hH : IsHyperlinear H) (ρ : G →* H) (hne : ∃ g : G, ρ g ≠ 1) :
    HasNontrivialHyperlinearQuotient G := by
  obtain ⟨g, hg⟩ := hne
  have hrange : IsHyperlinear ρ.range :=
    isHyperlinear_of_injective ρ.range.subtype Subtype.val_injective hH
  have hgne : ρ.rangeRestrict g ≠ 1 := by
    intro h
    apply hg
    simpa using congrArg Subtype.val h
  exact ⟨ρ.range, inferInstance, ρ.rangeRestrict,
    ρ.rangeRestrict_surjective, hrange, g, hgne⟩

/-- The group-theoretic conclusion of Kazhdan-corner extraction. -/
theorem HasHyperlinearCornerRepresentation.hasNontrivialHyperlinearQuotient
    (hcorner : HasHyperlinearCornerRepresentation G) :
    HasNontrivialHyperlinearQuotient G := by
  obtain ⟨H, hHGroup, hH, ρ, hne⟩ := hcorner
  letI : Group H := hHGroup
  exact hasNontrivialHyperlinearQuotient_of_hom hH ρ hne

/-- Closed positive control for the quotient formulation. -/
theorem hasNontrivialHyperlinearQuotient_cyclicTwo :
    HasNontrivialHyperlinearQuotient (Multiplicative (ZMod 2)) :=
  hasHyperlinearCornerRepresentation_cyclicTwo.hasNontrivialHyperlinearQuotient

/-! ## The analytic corner theorem -/

/-- **Kazhdan-corner theorem, representation form.**  A nontrivial
property-`(T)` weak-MF group admits a nontrivial homomorphism into a
hyperlinear group.

The target is the range of the canonical homomorphism into the tracial
ultraproduct of the diagonal moving-corner models. -/
theorem hasHyperlinearCornerRepresentation_of_kazhdan_weakMF
    {J : Type} [Group J] [Nontrivial J]
    (hT : HasKazhdanPropertyT.{0, 0} J) (hMF : IsWeakMF J) :
    HasHyperlinearCornerRepresentation J := by
  classical
  obtain ⟨S, _hone, _hsymm, hgen⟩ :=
    KazhdanFiniteGeneration.exists_symmetric_generating_finset J hT
  have hfg : Group.FG J := Group.fg_def.mpr ⟨S, hgen⟩
  letI : Countable J := countable_of_fg hfg
  obtain ⟨D⟩ := KazhdanCornerMatrices.exists_movingCornerSetup hT hMF
  obtain ⟨R⟩ := KazhdanCornerMatrices.exists_movingCornerSchedule D
  let U : Ultrafilter ℕ := Ultrafilter.of Filter.cofinite
  have hcof : ((U : Ultrafilter ℕ) : Filter ℕ) ≤ Filter.cofinite :=
    Ultrafilter.of_le Filter.cofinite
  let rho := R.hyperlinearHom hcof
  obtain ⟨g, _hgS, hg⟩ := R.exists_generator_hyperlinearHom_ne_one hcof
  have hrange : IsHyperlinear rho.range :=
    isHyperlinear_of_hyperlinearUltraproductEmbedding
      U R.model R.model_nonempty rho.range.subtype Subtype.val_injective
  have hgne : rho.rangeRestrict g ≠ 1 := by
    intro h
    apply hg
    simpa [rho] using congrArg Subtype.val h
  exact ⟨rho.range, inferInstance, hrange, rho.rangeRestrict, g, hgne⟩

/-- **Kazhdan-corner theorem, quotient form.**  Every nontrivial
property-`(T)` weak-MF group has a nontrivial hyperlinear quotient. -/
theorem hasNontrivialHyperlinearQuotient_of_kazhdan_weakMF
    {J : Type} [Group J] [Nontrivial J]
    (hT : HasKazhdanPropertyT.{0, 0} J) (hMF : IsWeakMF J) :
    HasNontrivialHyperlinearQuotient J :=
  HasHyperlinearCornerRepresentation.hasNontrivialHyperlinearQuotient
    (hasHyperlinearCornerRepresentation_of_kazhdan_weakMF hT hMF)

/-! ## Simplicity makes the corner faithful -/

/-- A simple group with a nontrivial hyperlinear quotient is hyperlinear: the
quotient map has a proper kernel, hence its kernel is trivial. -/
theorem isHyperlinear_of_simple_nontrivialHyperlinearQuotient [IsSimpleGroup G]
    (hq : HasNontrivialHyperlinearQuotient G) : IsHyperlinear G := by
  obtain ⟨Q, hQGroup, q, _hqsurj, hQ, g, hg⟩ := hq
  letI : Group Q := hQGroup
  have hqinj : Function.Injective q := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal q.ker inferInstance with
      hbot | htop
    · exact (MonoidHom.ker_eq_bot_iff q).mp hbot
    · exfalso
      apply hg
      have hmem : g ∈ q.ker := htop ▸ Subgroup.mem_top g
      simpa [MonoidHom.mem_ker] using hmem
  exact isHyperlinear_of_injective q hqinj hQ

/-- A nontrivial homomorphism from a simple group into a hyperlinear group is
injective, so the source group is hyperlinear. -/
theorem isHyperlinear_of_simple_hyperlinearCorner [IsSimpleGroup G]
    (hcorner : HasHyperlinearCornerRepresentation G) : IsHyperlinear G :=
  isHyperlinear_of_simple_nontrivialHyperlinearQuotient
    hcorner.hasNontrivialHyperlinearQuotient

/-- **Kazhdan-corner theorem, simple form.**  A simple property-`(T)` weak-MF
group is hyperlinear. -/
theorem isHyperlinear_of_simple_kazhdan_weakMF
    {J : Type} [Group J] [IsSimpleGroup J]
    (hT : HasKazhdanPropertyT.{0, 0} J) (hMF : IsWeakMF J) :
    IsHyperlinear J :=
  isHyperlinear_of_simple_nontrivialHyperlinearQuotient
    (hasNontrivialHyperlinearQuotient_of_kazhdan_weakMF hT hMF)

namespace KazhdanCorner

/-- **Single-certificate reduction.**  For a simple property-`(T)` nonsofic
group, one weak-MF certificate makes that same group hyperlinear while it
remains nonsofic. -/
theorem simple_candidate_profile
    {J : Type} [Group J] [IsSimpleGroup J]
    (hT : HasKazhdanPropertyT.{0, 0} J) (hns : ¬ IsSofic J)
    (hMF : IsWeakMF J) : IsHyperlinear J ∧ ¬ IsSofic J :=
  ⟨isHyperlinear_of_simple_kazhdan_weakMF hT hMF, hns⟩

end KazhdanCorner

end GroupApproximation
