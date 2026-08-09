import NonsoficGroupsExist.Kazhdan.Kazhdan
import NonsoficGroupsExist.Sofic.WeakMFUltraproduct
import Mathlib.GroupTheory.Subgroup.Simple

/-!
# The Kazhdan-corner reduction

This file isolates the exact formal content of the Kazhdan-corner argument for
operator-norm matricial approximations.

There are three layers.

* `IsWeakMF` is the local, uniformly separated operator-norm approximation
  property already represented by `IsNormApproximable`.
* `HasHyperlinearCornerRepresentation G` says that the analytic corner
  construction has produced a nontrivial homomorphism from `G` into a
  hyperlinear group.
* `KazhdanCornerPrinciple G` is the one named analytic principle: property
  `(T)` and weak-MF produce such a corner representation.

Everything after that analytic principle is proved here.  The range of the
corner representation is a nontrivial hyperlinear quotient.  If `G` is
simple, the representation is injective, hence `G` itself is hyperlinear.
Combining this with nonsoficity gives the single-certificate reduction for
Pestov's Question 3.4.

The principle is deliberately a named hypothesis rather than a theorem in
this file.  The constructive Kazhdan projection, the operator-norm
ultraproduct embedding, and the bridge from tracial ultraproduct embeddings to
the local predicate `IsHyperlinear` are now formalized in adjacent modules.
What remains is the finite-stage spectral-gap transfer, compression to the
moving spectral corner, and polar correction of the compressed blocks.
Packaging that remaining analytic theorem as a definition keeps the
dependency visible in every endpoint below; no axiom, `sorry`, or hidden
classical assertion is introduced.
-/

namespace NonsoficGroupsExist

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

/-! ## The named analytic principle -/

/-- **Kazhdan-corner principle.**  For this group, property `(T)` upgrades a
weak-MF operator-norm embedding to a nontrivial representation in a
hyperlinear group.

This is the exact analytic theorem described in `NOTEPAD.md`: cut the
operator-norm ultraproduct representation by the complement of the central
Kazhdan projection, normalize traces on that nonzero corner, and use the
Kazhdan Laplacian gap to make the resulting tracial representation
nontrivial. -/
def KazhdanCornerPrinciple (G : Type u) [Group G] : Prop :=
  HasKazhdanPropertyT.{u, u} G → IsWeakMF G →
    HasHyperlinearCornerRepresentation G

/-- Positive control: a nontrivial hyperlinear group satisfies the principle,
because its identity representation supplies the conclusion independently of
the two antecedents. -/
theorem kazhdanCornerPrinciple_of_isHyperlinear [Nontrivial G]
    (hG : IsHyperlinear G) : KazhdanCornerPrinciple G :=
  fun _ _ ↦ hasHyperlinearCornerRepresentation_of_isHyperlinear hG

/-- Closed positive control for the named analytic principle. -/
theorem kazhdanCornerPrinciple_cyclicTwo :
    KazhdanCornerPrinciple (Multiplicative (ZMod 2)) :=
  kazhdanCornerPrinciple_of_isHyperlinear
    (isHyperlinear_of_finite (Multiplicative (ZMod 2)))

/-- **Kazhdan-corner theorem, quotient form.**  Subject only to the named
analytic principle, every nontrivial property-`(T)` weak-MF group has a
nontrivial hyperlinear quotient. -/
theorem hasNontrivialHyperlinearQuotient_of_kazhdan_weakMF
    (hcorner : KazhdanCornerPrinciple G)
    (hT : HasKazhdanPropertyT.{u, u} G) (hMF : IsWeakMF G) :
    HasNontrivialHyperlinearQuotient G :=
  (hcorner hT hMF).hasNontrivialHyperlinearQuotient

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

/-- **Kazhdan-corner theorem, simple form.**  Under the named analytic
principle, a simple property-`(T)` weak-MF group is hyperlinear. -/
theorem isHyperlinear_of_simple_kazhdan_weakMF [IsSimpleGroup G]
    (hcorner : KazhdanCornerPrinciple G)
    (hT : HasKazhdanPropertyT.{u, u} G) (hMF : IsWeakMF G) :
    IsHyperlinear G :=
  isHyperlinear_of_simple_nontrivialHyperlinearQuotient
    (hasNontrivialHyperlinearQuotient_of_kazhdan_weakMF hcorner hT hMF)

namespace KazhdanCorner

/-- **Single-certificate reduction.**  For a simple property-`(T)` nonsofic
group satisfying the Kazhdan-corner principle, one weak-MF certificate makes
that same group hyperlinear while it remains nonsofic.  This is the exact
conditional profile needed for a negative answer to Pestov's Question 3.4;
it does not assert that the certificate exists. -/
theorem simple_candidate_profile
    {J : Type} [Group J] [IsSimpleGroup J]
    (hcorner : KazhdanCornerPrinciple J)
    (hT : HasKazhdanPropertyT.{0, 0} J) (hns : ¬ IsSofic J)
    (hMF : IsWeakMF J) : IsHyperlinear J ∧ ¬ IsSofic J :=
  ⟨isHyperlinear_of_simple_kazhdan_weakMF hcorner hT hMF, hns⟩

end KazhdanCorner

end NonsoficGroupsExist
