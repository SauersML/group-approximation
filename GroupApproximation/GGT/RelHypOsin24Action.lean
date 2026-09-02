import GroupApproximation.GGT.RelHypOsin24SuitabilityGlue
import GroupApproximation.GGT.ElementaryMorseAlphabet
import GroupApproximation.GGT.HullSCUnionGeometryHyperbolicFactor

/-!
# The Hull action attached to a relatively hyperbolic suitable subgroup

The one-step Hull construction needs a `HullGeneratingSet` on which the given
subgroup is suitable.  For a relatively hyperbolic pair the intended alphabet
is the labelled relative alphabet `X ⊔ ⨆ H_lambda` itself.

Two standard relative-Cayley facts are isolated below:

* finite relative base plus hyperbolic embeddedness makes the relative Cayley
  action acylindrical; and
* a non-parabolic element of infinite order is loxodromic on that graph.

They are the action and element forms of Osin's relative-hyperbolic
classification.  Once supplied, the rest is proved here.  Osin suitability
gives two non-commensurable infinite-order non-parabolic elements.  The second
fact makes them loxodromic, and the proved acylindrical common-power theorem
turns non-commensurability into independence.  The finite-normalizer clause is
`IsSuitableSubgroup.normalizesNoNontrivialFinite`.

The empty-peripheral theorems are model tests: then the relative alphabet is a
finite ordinary alphabet, so both action facts reduce to existing proper-Cayley
theorems.
-/

namespace GroupApproximation
namespace GGT
namespace RelHyp

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u v

/-! ## The two relative-Cayley facts -/

/-- The relative Cayley action of a strongly relatively hyperbolic structure
with finite relative base is acylindrical. -/
def RelHypFiniteBaseAcylindricityStatement : Prop :=
  ∀ (G : Type u) (_ : Group G) (I : Type v) (D : RelGenSet G I),
    D.base.Finite → D.IsHyperbolicallyEmbedded →
      IsAcylindrical G (Cayley D.alphabet)

/-- An infinite-order non-parabolic element is loxodromic on the finite-base
relative Cayley graph. -/
def RelHypHyperbolicElementLoxodromicStatement : Prop :=
  ∀ (G : Type u) (_ : Group G) (I : Type v) (D : RelGenSet G I),
    D.base.Finite → D.IsHyperbolicallyEmbedded →
      ∀ g : G, IsHyperbolicElement D.fam g →
        (∀ n : ℕ, 0 < n → g ^ n ≠ 1) →
          IsLoxodromic g (Cayley.base D.alphabet)

/-! ## Empty-family model tests -/

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

/-- The acylindricity statement has the ordinary finite-Cayley model when the
peripheral family is empty. -/
theorem relHypFiniteBaseAcylindricity_emptyModel
    {G : Type u} [Group G] {I : Type v} [IsEmpty I]
    (D : RelGenSet G I) (hfinite : D.base.Finite) :
    IsAcylindrical G (Cayley D.alphabet) :=
  isAcylindrical_cayley_of_finite D.alphabet
    (relGenSet_alphabet_finite_of_isEmpty D hfinite)

/-- The loxodromic classification statement likewise reduces to the proved
finite-Cayley infinite-order theorem for the empty family. -/
theorem relHypHyperbolicElementLoxodromic_emptyModel
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
  /-- Hull's generating set on the same relative Cayley graph. -/
  hull : HullGeneratingSet G
  /-- The two alphabets agree literally. -/
  hull_alphabet : hull.alphabet = rel.alphabet
  /-- The subgroup is suitable for Hull's action. -/
  suitable : Suitable hull.alphabet H

/-- The two relative-Cayley facts turn Osin suitability into Hull suitability
on the original labelled relative Cayley graph. -/
theorem exists_relativeHullData_of_actionBridges
    (hacyBridge : RelHypFiniteBaseAcylindricityStatement.{u, v})
    (hloxBridge : RelHypHyperbolicElementLoxodromicStatement.{u, v})
    {G : Type u} [Group G] {I : Type v} {Hfam : I → Subgroup G}
    (hrel : IsRelativelyHyperbolic G Hfam) (H : Subgroup G)
    (hsuit : IsSuitableSubgroup Hfam H) :
    Nonempty (RelativeHullData Hfam H) := by
  obtain ⟨D, hfinite, hfam, hemb⟩ := hrel
  obtain ⟨delta, hdelta⟩ := hemb.hyperbolic
  have hacy : IsAcylindrical G (Cayley D.alphabet) :=
    hacyBridge G inferInstance I D hfinite hemb
  have hnormal : HullSuitable.NormalizesNoNontrivialFinite H :=
    hsuit.normalizesNoNontrivialFinite
  obtain ⟨f₁, hf₁, f₂, hf₂, hhyper₁, hhyper₂,
    hord₁, hord₂, hnc, _hinter⟩ := hsuit
  have hhyper₁D : IsHyperbolicElement D.fam f₁ := by
    rw [hfam]
    exact hhyper₁
  have hhyper₂D : IsHyperbolicElement D.fam f₂ := by
    rw [hfam]
    exact hhyper₂
  have hlox₁ : IsLoxodromic f₁ (Cayley.base D.alphabet) :=
    hloxBridge G inferInstance I D hfinite hemb f₁ hhyper₁D hord₁
  have hlox₂ : IsLoxodromic f₂ (Cayley.base D.alphabet) :=
    hloxBridge G inferInstance I D hfinite hemb f₂ hhyper₂D hord₂
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
    hull_alphabet := rfl
    suitable := hHullSuitable }⟩

end RelHyp
end GGT
end GroupApproximation
