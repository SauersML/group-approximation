import GroupApproximation.GGT.RelHypOsin24Action
import GroupApproximation.GGT.HullSCUnionGeometryHyperbolicFactor

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
    (hemb : D.IsHyperbolicallyEmbedded) (g : G)
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

end RelHyp
end GGT
end GroupApproximation
