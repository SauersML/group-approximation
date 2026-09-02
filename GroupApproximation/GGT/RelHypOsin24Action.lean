import GroupApproximation.GGT.RelHypOsin24SuitabilityGlue
import GroupApproximation.GGT.ElementaryMorseAlphabet
import GroupApproximation.GGT.HullSCUnionGeometryHyperbolicFactor

/-!
# The Hull action attached to a relatively hyperbolic suitable subgroup

The one-step Hull construction needs a `HullGeneratingSet` on which the given
subgroup is suitable, while its arbitrary original peripheral family must be
preserved on the same alphabet.  `RelativeHullData` is that compatibility
object.

`CompatibleRelativeHullActionStatement` is the precise pre-quotient frontier.
It is strictly smaller than Osin's quotient theorem: it mentions no quotient,
target, relator, kernel, peripheral image, torsion lift, or suitability
preservation.  For a genuine Osin relative presentation it is the action form
of the element classification together with Lemma 2.3.

The finite-base hyperbolically embedded predicate alone does not justify
acylindricity of its raw relative Cayley graph at an arbitrary index type.
DGO Proposition 4.28(b) assumes a finite family, and Osin Theorem 5.4 enlarges
the base before asserting acylindricity.  The empty-peripheral theorem below is
the positive model: the alphabet is finite, so the compatible Hull action is
constructed entirely from existing finite-Cayley results.
-/

namespace GroupApproximation
namespace GGT
namespace RelHyp

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u v

/-! ## Empty-family finite-Cayley facts -/

/-- With no peripheral indices the full relative alphabet is the finite base. -/
theorem relGenSet_alphabet_finite_of_isEmpty
    {G : Type u} [Group G] {I : Type v} [IsEmpty I]
    (D : RelGenSet G I) (hfinite : D.base.Finite) :
    D.alphabet.carrier.Finite := by
  have hempty : (⋃ i : I, ((D.fam i : Subgroup G) : Set G)) = ∅ :=
    Set.iUnion_of_empty _
  rw [show D.alphabet.carrier =
      D.base ∪ ⋃ i : I, ((D.fam i : Subgroup G) : Set G) by rfl,
    hempty, Set.union_empty]
  exact hfinite

/-- The ordinary finite-Cayley action is acylindrical when the peripheral
family is empty. -/
theorem relHypFiniteBaseAcylindricity_empty
    {G : Type u} [Group G] {I : Type v} [IsEmpty I]
    (D : RelGenSet G I) (hfinite : D.base.Finite) :
    IsAcylindrical G (Cayley D.alphabet) :=
  isAcylindrical_cayley_of_finite D.alphabet
    (relGenSet_alphabet_finite_of_isEmpty D hfinite)

/-- Infinite-order elements are loxodromic in the empty-family model. -/
theorem relHypHyperbolicElementLoxodromic_empty
    {G : Type u} [Group G] {I : Type v} [IsEmpty I]
    (D : RelGenSet G I) (hfinite : D.base.Finite)
    (hemb : D.IsHyperbolicallyEmbedded) (g : G)
    (hord : ∀ n : ℕ, 0 < n → g ^ n ≠ 1) :
    IsLoxodromic g (Cayley.base D.alphabet) := by
  have hnot : ¬ IsOfFinOrder g := by
    intro hfin
    obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp hfin
    exact hord n hn hpow
  obtain ⟨delta, hdelta⟩ := hemb.hyperbolic
  exact HullSCUnionGeometry.isLoxodromic_cayley_of_not_isOfFinOrder
    D.alphabet (relGenSet_alphabet_finite_of_isEmpty D hfinite)
      hdelta hnot

/-! ## Assembly of Hull's action and suitability -/

/-- The relative structure and Hull generating set attached to one Osin
suitable subgroup. -/
structure RelativeHullData
    {G : Type u} [Group G] {I : Type v}
    (Hfam : I → Subgroup G) (H : Subgroup G) where
  /-- The finite-base relative structure. -/
  rel : RelGenSet G I
  /-- The relative base is finite. -/
  base_finite : rel.base.Finite
  /-- Its labelled family is the requested family. -/
  fam_eq : rel.fam = Hfam
  /-- The original family is hyperbolically embedded. -/
  embedded : rel.IsHyperbolicallyEmbedded
  /-- Hull's generating set containing the finite-base relative alphabet. -/
  hull : HullGeneratingSet G
  /-- Every original relative letter is available in Hull's alphabet. -/
  rel_alphabet_subset : rel.alphabet.carrier ⊆ hull.alphabet.carrier
  /-- The subgroup is suitable for Hull's action. -/
  suitable : Suitable hull.alphabet H

/-- **The compatible action form of Osin Lemma 2.3.**

The output keeps the original labelled relative structure and equips an
alphabet containing it with Hull's hyperbolic, acylindrical, non-elementary
data so that the given subgroup is suitable.  This is the sole pre-quotient
geometric input of the Hull specialization. -/
def CompatibleRelativeHullActionStatement : Prop :=
  ∀ (G : Type u) (_ : Group G) (I : Type v)
    (Hfam : I → Subgroup G), IsRelativelyHyperbolic G Hfam →
      ∀ H : Subgroup G, IsSuitableSubgroup Hfam H →
        Nonempty (RelativeHullData Hfam H)

/-- The compatible-action statement has its ordinary hyperbolic-group model:
with no peripherals, the finite relative base is a finite Cayley alphabet,
and Osin suitability itself supplies the independent loxodromic pair. -/
theorem nonempty_relativeHullData_emptyModel
    {G : Type u} [Group G] {I : Type v} [IsEmpty I]
    {Hfam : I → Subgroup G} (hrel : IsRelativelyHyperbolic G Hfam)
    (H : Subgroup G) (hsuit : IsSuitableSubgroup Hfam H) :
    Nonempty (RelativeHullData Hfam H) := by
  obtain ⟨D, hfinite, hfam, hemb⟩ := hrel
  obtain ⟨delta, hdelta⟩ := hemb.hyperbolic
  have hacy : IsAcylindrical G (Cayley D.alphabet) :=
    relHypFiniteBaseAcylindricity_empty D hfinite
  have hnormal : HullSuitable.NormalizesNoNontrivialFinite H :=
    hsuit.normalizesNoNontrivialFinite
  obtain ⟨f₁, hf₁, f₂, hf₂, _hhyper₁, _hhyper₂,
    hord₁, hord₂, hnc, _hinter⟩ := hsuit
  have hlox₁ : IsLoxodromic f₁ (Cayley.base D.alphabet) :=
    relHypHyperbolicElementLoxodromic_empty D hfinite hemb f₁ hord₁
  have hlox₂ : IsLoxodromic f₂ (Cayley.base D.alphabet) :=
    relHypHyperbolicElementLoxodromic_empty D hfinite hemb f₂ hord₂
  have hnoPower : ∀ p q : ℤ, p ≠ 0 → q ≠ 0 → f₁ ^ p ≠ f₂ ^ q := by
    intro p q hp hq heq
    apply hnc
    refine ⟨p, q, 1, hp, hq, ?_⟩
    simpa using heq
  have hindTheory : Elementary.IndependentOfNoCommonZpow G
      (Cayley.base D.alphabet) :=
    ElementaryMorse.independentOfNoCommonZpow_cayley_of_hyperbolic
      D.alphabet hdelta hacy
  have hind : Independent f₁ f₂ (Cayley.base D.alphabet) :=
    hindTheory f₁ f₂ hlox₁ hlox₂ hnoPower
  have hactsH : ActsNonElementarily H (Cayley.base D.alphabet) :=
    ⟨f₁, hf₁, f₂, hf₂, hlox₁, hlox₂, hind⟩
  have hactsTop : ActsNonElementarily (⊤ : Subgroup G)
      (Cayley.base D.alphabet) :=
    ⟨f₁, Subgroup.mem_top f₁, f₂, Subgroup.mem_top f₂,
      hlox₁, hlox₂, hind⟩
  let A : HullGeneratingSet G :=
    { alphabet := D.alphabet
      delta := delta
      hyperbolic := hdelta
      acylindrical := hacy
      nonElementary := hactsTop }
  have hHullSuitable : Suitable A.alphabet H :=
    ⟨hactsH, hnormal⟩
  exact ⟨{
    rel := D
    base_finite := hfinite
    fam_eq := hfam
    embedded := hemb
    hull := A
    rel_alphabet_subset := Set.Subset.rfl
    suitable := hHullSuitable }⟩

end RelHyp
end GGT
end GroupApproximation
