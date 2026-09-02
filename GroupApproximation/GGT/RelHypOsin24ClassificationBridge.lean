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

/-! ### The missing finite-base binder is load-bearing

The source theorem is a theorem for a finite relative generating set.  The
hyperbolically embedded predicate by itself allows an infinite base, and then
the positive-power conclusion is false even with an empty peripheral family:
take the whole group as the base alphabet.  This model is the direct analogue
of Osin's `K × ℤ` warning before Theorem 5.4, with the peripheral index empty.
The refutation is kept next to the named statement so no downstream theorem can
silently use the uncorrected quantifier order.
 -/

def infiniteBaseEmptyRelGenSet : RelGenSet (Multiplicative ℤ) Empty where
  base := Set.univ
  fam := Empty.elim
  symmetricGenerating := by
    constructor
    · intro x _hx
      exact Set.mem_univ x⁻¹
    · rw [eq_top_iff]
      intro x _hx
      exact Subgroup.subset_closure (Or.inl (Set.mem_univ x))

theorem infiniteBaseEmptyRelGenSet_alphabet_carrier :
    infiniteBaseEmptyRelGenSet.alphabet.carrier = Set.univ := by
  ext x
  constructor
  · intro _
    exact Set.mem_univ x
  · intro _
    exact Set.mem_union_left _ (Set.mem_univ x)

theorem infiniteBaseEmptyRelGenSet_hyperbolicallyEmbedded :
    infiniteBaseEmptyRelGenSet.IsHyperbolicallyEmbedded := by
  refine ⟨?_, ?_⟩
  · rw [infiniteBaseEmptyRelGenSet_alphabet_carrier]
    exact isHyperbolicSpace_of_bounded (by
      intro x y
      have hmem : ((Cayley.val x)⁻¹ * Cayley.val y : Multiplicative ℤ) ∈
          (Set.univ : Set (Multiplicative ℤ)) := Set.mem_univ _
      have hnorm : WordMetric.wordNorm (Set.univ : Set (Multiplicative ℤ))
          ((Cayley.val x)⁻¹ * Cayley.val y) ≤ 1 :=
        WordMetric.wordNorm_le_one_of_mem hmem
      rw [Cayley.dist_eq]
      exact_mod_cast hnorm)
  · intro e
    exact Empty.elim e

theorem infiniteBaseEmptyRelGenSet_all_powers_bounded (g : Multiplicative ℤ) :
    ∀ n : ℕ, dist (Cayley.base infiniteBaseEmptyRelGenSet.alphabet)
      ((g ^ n) • Cayley.base infiniteBaseEmptyRelGenSet.alphabet) ≤ (1 : ℝ) := by
  intro n
  rw [infiniteBaseEmptyRelGenSet_alphabet_carrier]
  have hmem : (g ^ n : Multiplicative ℤ) ∈
      (Set.univ : Set (Multiplicative ℤ)) := Set.mem_univ _
  have hnorm : WordMetric.wordNorm (Set.univ : Set (Multiplicative ℤ))
      (g ^ n) ≤ 1 := WordMetric.wordNorm_le_one_of_mem hmem
  rw [Cayley.dist_eq, WordMetric.wordDist_one_left]
  exact_mod_cast hnorm

theorem not_isEscaping_of_infiniteBaseEmptyRelGenSet (g : Multiplicative ℤ) :
    ¬ IsEscaping g (Cayley.base infiniteBaseEmptyRelGenSet.alphabet) := by
  intro hesc
  have hev := hesc.eventually_ge_atTop (2 : ℝ)
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  have hbad := hN N (le_refl N)
  have hbound := infiniteBaseEmptyRelGenSet_all_powers_bounded g N
  linarith

theorem not_relativePowerEscapeStatement :
    ¬ RelativePowerEscapeStatement.{0, 0} := by
  intro hEscape
  let g : Multiplicative ℤ := Multiplicative.ofAdd 1
  have hpow : ∀ n : ℕ, 0 < n → g ^ n ≠ 1 := by
    intro n hn hzero
    have hcast : (n : ℤ) = 0 := by
      exact_mod_cast congrArg Multiplicative.toAdd hzero
    omega
  have hhyper : IsHyperbolicElement infiniteBaseEmptyRelGenSet.fam g :=
    isHyperbolicElement_of_isEmpty infiniteBaseEmptyRelGenSet.fam g
  have hesc := hEscape (Multiplicative ℤ) inferInstance Empty
    infiniteBaseEmptyRelGenSet infiniteBaseEmptyRelGenSet_hyperbolicallyEmbedded
      g hhyper hpow
  exact not_isEscaping_of_infiniteBaseEmptyRelGenSet g hesc

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

/-- **Relative escaping-to-loxodromic bridge.**  This is the action-theoretic
half of the element theorem, isolated as a strictly smaller named Prop: it
assumes the orbit already escapes and asks only for the loxodromic conclusion
under an acylindrical hyperbolic relative Cayley action. -/
def RelativeEscapingLoxodromicBridgeStatement : Prop :=
  ∀ (G : Type u) (_ : Group G) (I : Type v) (D : RelGenSet G I),
    D.IsHyperbolicallyEmbedded →
      IsAcylindrical G (Cayley D.alphabet) → ∀ g : G,
        IsEscaping g (Cayley.base D.alphabet) →
          IsLoxodromic g (Cayley.base D.alphabet)

/-- The relative escaping-to-loxodromic bridge is Bowditch's theorem for the
hyperbolic Cayley graph supplied by the hyperbolically embedded structure. -/
theorem relativeEscapingLoxodromicBridge_proved :
    RelativeEscapingLoxodromicBridgeStatement.{u, v} := by
  intro G instG I D hD hacy g hesc
  letI : Group G := instG
  exact isLoxodromic_of_relativePowerEscape_of_acylindrical D hD hacy hesc

/-- Model test for the bridge: the finite empty-family action is acylindrical,
and its infinite-order powers escape by finite properness. -/
theorem relativeEscapingLoxodromicBridge_emptyModel
    {G : Type u} [Group G] {I : Type v} [IsEmpty I]
    (D : RelGenSet G I) (hfinite : D.base.Finite)
    (hemb : D.IsHyperbolicallyEmbedded) (g : G)
    (hord : ∀ n : ℕ, 0 < n → g ^ n ≠ 1) :
    IsLoxodromic g (Cayley.base D.alphabet) := by
  apply relativeEscapingLoxodromicBridge_proved G inferInstance I D hemb
    (relHypFiniteBaseAcylindricity_empty D hfinite) g
  exact relativePowerEscape_emptyModel D hfinite hemb g hord

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
