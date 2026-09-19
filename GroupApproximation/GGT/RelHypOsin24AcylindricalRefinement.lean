import GroupApproximation.GGT.RelHypDefinition
import GroupApproximation.GGT.HullSCCanonicalQuotientPublished

/-!
# The finite-family acylindrical refinement used around Osin's Theorem 2.4

Osin's Theorem 5.4 does not say that the action on an initially supplied
relative Cayley graph is acylindrical.  For a finite hyperbolically embedded
family it enlarges the relative base, preserves the labelled family and its
relative metrics, and makes the action on the enlarged relative Cayley graph
acylindrical.

This module packages exactly that output and applies the theorem already proved
in `OsinTheorem54Unconditional`.  The finite-family binder is explicit: DGO
Proposition 4.28(b) and Osin Theorem 5.4 both require it in the converse and
enlargement directions used here.
-/

namespace GroupApproximation
namespace GGT
namespace RelHyp

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u v

/-- An Osin 5.4 enlargement of one labelled relative generating set. -/
structure AcylindricalRelativeRefinement
    {G : Type u} [Group G] {I : Type v} (D : RelGenSet G I) where
  /-- The enlarged relative generating set. -/
  rel : RelGenSet G I
  /-- The old base is contained in the enlarged base. -/
  base_subset : D.base ⊆ rel.base
  /-- Peripheral labels and subgroups are unchanged. -/
  fam_eq : rel.fam = D.fam
  /-- Hyperbolic embeddedness survives the enlargement. -/
  embedded : rel.IsHyperbolicallyEmbedded
  /-- The enlarged relative Cayley action is acylindrical. -/
  acylindrical : IsAcylindrical G (Cayley rel.alphabet)

/-- **Osin, Theorem 5.4**, applied to a finite labelled family. -/
theorem exists_acylindricalRelativeRefinement
    {G : Type u} [Group G] {I : Type v} [Finite I]
    (D : RelGenSet G I) (hemb : D.IsHyperbolicallyEmbedded) :
    Nonempty (AcylindricalRelativeRefinement D) := by
  obtain ⟨E, hbase, hfam, hembE, hacy⟩ :=
    OsinEnlargement.osinTheorem54Fam_unconditional G I D hemb
  exact ⟨{
    rel := E
    base_subset := hbase
    fam_eq := hfam
    embedded := hembE
    acylindrical := hacy }⟩

/-- A finite-index instance of the repository's relative-hyperbolicity
predicate has an acylindrical refinement with the same peripheral family. -/
theorem exists_acylindricalRelativeRefinement_of_isRelativelyHyperbolic
    {G : Type u} [Group G] {I : Type v} [Finite I]
    {Hfam : I → Subgroup G} (hrel : IsRelativelyHyperbolic G Hfam) :
    ∃ (D : RelGenSet G I), D.base.Finite ∧ D.fam = Hfam ∧
      Nonempty (AcylindricalRelativeRefinement D) := by
  obtain ⟨D, hfinite, hfam, hemb⟩ := hrel
  exact ⟨D, hfinite, hfam,
    exists_acylindricalRelativeRefinement D hemb⟩

/-- The empty-family model reduces Osin's enlargement to the theorem itself;
the output remains meaningful and its peripheral equality is vacuous. -/
theorem acylindricalRelativeRefinement_emptyModel
    {G : Type u} [Group G] (D : RelGenSet G Empty)
    (hemb : D.IsHyperbolicallyEmbedded) :
    Nonempty (AcylindricalRelativeRefinement D) :=
  exists_acylindricalRelativeRefinement D hemb

end RelHyp
end GGT
end GroupApproximation
