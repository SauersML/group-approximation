import GroupApproximation.GGT.RelHypOsin24Action
import GroupApproximation.GGT.HullSCUnionGeometryHyperbolicFactor
import GroupApproximation.GGT.HullYiAlphabetTransfer
import GroupApproximation.GGT.OsinTheorem54Unconditional

/-!
# The escape-to-loxodromy bridge for Osin's element classification

Osin's relative element theorem is the power-growth statement preceding his
small-cancellation theorem: a hyperbolic (non-parabolic) element of infinite
order has a relative orbit escaping every bounded set.  In the Memoirs version
this is the linear estimate for powers (Theorem 1.10, with the relative
geodesic and component lemmas in §4).  The present file isolates its weaker
conclusion, `RelativePowerEscapeStatement`, and proves all consequences that
use only the action theory already in the repository.

The escape estimate is strictly weaker than `IsLoxodromic`: loxodromy supplies
escape by `IsLoxodromic.isEscaping`, while the converse needs hyperbolicity and
acylindricity.  The latter implication is the proved Bowditch bridge
`HullSCUnionGeometry.escapingIsLoxodromic_cayley_of_acylindrical`.  Thus an
acylindrical relative Cayley graph gets the desired element classification from
the escape estimate.  The remaining general-index theorem is exactly the
source proof of `RelativePowerEscapeStatement`; no claim that its relative
geodesic estimate has been reconstructed is made here.

The empty-family finite-base theorem is the model test.  There the relative
alphabet is finite, so properness gives escape of every infinite-order element,
and the existing finite-Cayley theorem gives loxodromy.
 -/

namespace GroupApproximation
namespace GGT
namespace RelHyp

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u v

/-! ## Osin's strictly smaller escape estimate -/

/-- **Relative power escape.**  This is the weak conclusion of Osin's linear
power estimate: a hyperbolic element of infinite order eventually leaves every
bounded subset of the relative Cayley graph.  It is strictly weaker than
`HyperbolicElementLoxodromicStatement`, since every loxodromic orbit escapes by
`IsLoxodromic.isEscaping` but no converse is asserted here. -/
def RelativePowerEscapeStatement : Prop :=
  ∀ (G : Type u) (_ : Group G) (I : Type v) (D : RelGenSet G I),
    D.IsHyperbolicallyEmbedded → ∀ g : G,
      IsHyperbolicElement D.fam g →
        (∀ n : ℕ, 0 < n → g ^ n ≠ 1) →
          IsEscaping g (Cayley.base D.alphabet)

/-- The finite empty-family model of relative power escape.  This is the model
test required for the named estimate: its proof is ordinary properness of a
finite Cayley graph, followed by no relative-component argument. -/
theorem relativePowerEscape_emptyModel
    {G : Type u} [Group G] {I : Type v} [IsEmpty I]
    (D : RelGenSet G I) (hfinite : D.base.Finite)
    (_hemb : D.IsHyperbolicallyEmbedded) (g : G)
    (hord : ∀ n : ℕ, 0 < n → g ^ n ≠ 1) :
    IsEscaping g (Cayley.base D.alphabet) := by
  have hnot : ¬ IsOfFinOrder g := by
    intro hfin
    obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp hfin
    exact hord n hn hpow
  exact HullSCUnionGeometry.isEscaping_cayley_of_not_isOfFinOrder D.alphabet
    (relGenSet_alphabet_finite_of_isEmpty D hfinite) hnot

/-- The one-point model is vacuous in the expected way: there are no
infinite-order elements, so the escape conclusion follows from the order
hypothesis. -/
theorem relativePowerEscape_trivialModel
    {I : Type v} [IsEmpty I] (D : RelGenSet PUnit I) (g : PUnit)
    (hord : ∀ n : ℕ, 0 < n → g ^ n ≠ 1) :
    IsEscaping g (Cayley.base D.alphabet) := by
  exfalso
  obtain ⟨n, hn⟩ : ∃ n : ℕ, 0 < n := ⟨1, by omega⟩
  exact hord n hn (Subsingleton.elim _ _)

/-! ## The action-theoretic bridge -/

/-- Escape implies loxodromy on a hyperbolic acylindrical relative Cayley
graph.  This is exactly the Bowditch half already proved in
`HullSCUnionGeometryHyperbolicFactor`. -/
theorem isLoxodromic_of_relativePowerEscape_of_acylindrical
    {G : Type u} [Group G] {I : Type v} (D : RelGenSet G I)
    (hemb : D.IsHyperbolicallyEmbedded)
    (hacy : IsAcylindrical G (Cayley D.alphabet)) {g : G}
    (hesc : IsEscaping g (Cayley.base D.alphabet)) :
    IsLoxodromic g (Cayley.base D.alphabet) := by
  obtain ⟨delta, hdelta⟩ := hemb.hyperbolic
  exact HullSCUnionGeometry.escapingIsLoxodromic_cayley_of_acylindrical
    D.alphabet hdelta hacy g hesc

/-- The classification theorem restricted to an already acylindrical relative
alphabet.  It is a strictly smaller target than the arbitrary-alphabet
`HyperbolicElementLoxodromicStatement`, so the only new input is the relative
power escape estimate. -/
def HyperbolicElementLoxodromicAcylindricalStatement : Prop :=
  ∀ (G : Type u) (_ : Group G) (I : Type v) (D : RelGenSet G I),
    D.IsHyperbolicallyEmbedded →
      IsAcylindrical G (Cayley D.alphabet) → ∀ g : G,
        IsHyperbolicElement D.fam g →
          (∀ n : ℕ, 0 < n → g ^ n ≠ 1) →
            IsLoxodromic g (Cayley.base D.alphabet)

/-- The relative escape estimate proves the acylindrical classification by the
one action-theoretic bridge above. -/
theorem hyperbolicElementLoxodromicAcylindrical_of_relativePowerEscape
    (hEscape : RelativePowerEscapeStatement.{u, v}) :
    HyperbolicElementLoxodromicAcylindricalStatement.{u, v} := by
  intro G instG I D hemb hacy g hhyper hord
  letI : Group G := instG
  exact isLoxodromic_of_relativePowerEscape_of_acylindrical D hemb hacy
    (hEscape G instG I D hemb g hhyper hord)

/-- Model test for the acylindrical classification: in the finite empty-family
case the action is acylindrical by finite properness, and the preceding escape
model gives loxodromy. -/
theorem hyperbolicElementLoxodromicAcylindrical_emptyModel
    {G : Type u} [Group G] {I : Type v} [IsEmpty I]
    (D : RelGenSet G I) (hfinite : D.base.Finite)
    (hemb : D.IsHyperbolicallyEmbedded) (g : G)
    (hord : ∀ n : ℕ, 0 < n → g ^ n ≠ 1) :
    IsLoxodromic g (Cayley.base D.alphabet) := by
  exact isLoxodromic_of_relativePowerEscape_of_acylindrical D hemb
    (relHypFiniteBaseAcylindricity_empty D hfinite)
    (relativePowerEscape_emptyModel D hfinite hemb g hord)

/-! ## Theorem 5.4 reduction of the arbitrary-alphabet target -/

/-- The empty labelled family whose base is the complete original relative
alphabet.  Its only purpose here is to feed Osin's Theorem 5.4, so the output
alphabet contains every original labelled letter. -/
def classificationEmptyFamilyRelGenSet {G : Type u} [Group G] {I : Type v}
    (D : RelGenSet G I) : RelGenSet G (ULift.{v} Empty) where
  base := D.alphabet.carrier
  fam := fun e => Empty.elim e.down
  symmetricGenerating := by
    change IsSymmetricGeneratingSet
      (D.alphabet.carrier ∪
        ⋃ e : ULift.{v} Empty, ((Empty.elim e.down : Subgroup G) : Set G))
    rw [Set.iUnion_of_empty, Set.union_empty]
    exact D.alphabet.symmetricGenerating

theorem classificationEmptyFamilyRelGenSet_alphabet
    {G : Type u} [Group G] {I : Type v} (D : RelGenSet G I) :
    (classificationEmptyFamilyRelGenSet D).alphabet = D.alphabet := by
  apply OsinComponents.alphabet_eq_of_carrier_eq
  change D.alphabet.carrier ∪
      ⋃ e : ULift.{v} Empty, ((Empty.elim e.down : Subgroup G) : Set G) =
        D.alphabet.carrier
  rw [Set.iUnion_of_empty, Set.union_empty]

theorem classificationEmptyFamilyRelGenSet_embedded
    {G : Type u} [Group G] {I : Type v} (D : RelGenSet G I)
    (hD : D.IsHyperbolicallyEmbedded) :
    (classificationEmptyFamilyRelGenSet D).IsHyperbolicallyEmbedded := by
  refine ⟨?_, ?_⟩
  · rw [classificationEmptyFamilyRelGenSet_alphabet D]
    exact hD.hyperbolic
  · intro e
    exact Empty.elim e.down

/-- Theorem 5.4 supplies an acylindrical empty-family alphabet containing the
original relative alphabet. -/
theorem exists_classificationAcylindricalOutput
    {G : Type u} [Group G] {I : Type v} (D : RelGenSet G I)
    (hD : D.IsHyperbolicallyEmbedded) :
    ∃ (E : RelGenSet G (ULift.{v} Empty)),
      D.alphabet.carrier ⊆ E.alphabet.carrier ∧
        E.IsHyperbolicallyEmbedded ∧
          IsAcylindrical G (Cayley E.alphabet) := by
  obtain ⟨E, hbase, _hfam, hE, hacy⟩ :=
    OsinEnlargement.osinTheorem54Fam_unconditional G (ULift.{v} Empty)
      (classificationEmptyFamilyRelGenSet D)
      (classificationEmptyFamilyRelGenSet_embedded D hD)
  have hcontain : D.alphabet.carrier ⊆ E.alphabet.carrier := by
    intro x hx
    exact Or.inl (hbase hx)
  exact ⟨E, hcontain, hE, hacy⟩

/-- The full one-element loxodromic conclusion follows from the smaller escape
estimate: enlarge to the empty family by Theorem 5.4, use the acylindrical
escape-to-loxodromy bridge there, and transfer loxodromy down to the original
alphabet by Hull's Lemma A.1. -/
theorem hyperbolicElementLoxodromic_of_relativePowerEscape
    (hEscape : RelativePowerEscapeStatement.{u, v}) :
    ∀ (G : Type u) (_ : Group G) (I : Type v) (D : RelGenSet G I),
      D.IsHyperbolicallyEmbedded → ∀ g : G,
        IsHyperbolicElement D.fam g →
          (∀ n : ℕ, 0 < n → g ^ n ≠ 1) →
            IsLoxodromic g (Cayley.base D.alphabet) := by
  intro G instG I D hD g hhyper hord
  letI : Group G := instG
  obtain ⟨E, hcontain, hE, hacy⟩ := exists_classificationAcylindricalOutput D hD
  have hhyperE : IsHyperbolicElement E.fam g :=
    isHyperbolicElement_of_isEmpty E.fam g
  have hescE : IsEscaping g (Cayley.base E.alphabet) :=
    hEscape G instG (ULift.{v} Empty) E hE g hhyperE hord
  have hloxE : IsLoxodromic g (Cayley.base E.alphabet) :=
    isLoxodromic_of_relativePowerEscape_of_acylindrical E hE hacy hescE
  exact HullSC.isLoxodromic_base_of_subset hcontain hloxE

end RelHyp
end GGT
end GroupApproximation
