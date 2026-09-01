import GroupApproximation.GGT.HullSCLemma49PowerDiagram
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.FreeGroup.Basic

/-!
# The Greendlinger interface for Hull's Lemma 4.9

Hull's printed Lemma 4.9 uses the estimating-graph argument from the relative
van Kampen diagram.  The algebraic development before that argument already
stores an oriented reduced power diagram and a geodesic word on its designated
outer cycle.  This file records the one remaining local output of the
estimating graph: either the outer word can be shortened modulo conjugacy, or
one relator exposes a prime piece that is too long.  The second theorem below
turns that output into the power correction required by the statement in
`HullSCLemma49PowerDiagram`.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.WordMetric

universe u w

/-- A chosen outer cycle for an oriented reduced power diagram.  Its word is
geodesic from the identity to `g`, and its repeated value is the product of
the oriented cell values, so it is the boundary cycle used by the relative
van Kampen diagram. -/
structure Lemma49DesignatedBoundaryCycle
    {G : Type u} [Group G] {Λ : Type w}
    (D : GGT.RelGenSet G Λ)
    (V : Set (List (GGT.RelLetter G Λ)))
    (cells : List (Lemma44OrientedRelatorCell V))
    (g : G) (n : ℕ) where
  word : List (GGT.RelLetter G Λ)
  geodesic : GGT.OsinComponents.IsGeodesicWord D 1 g word
  cycle_value :
    GGT.RelLetter.listVal (lemma49BoundaryPower word n) =
      (cells.map Lemma44OrientedRelatorCell.value).prod

/-- One local alternative supplied by the Greendlinger cell on the designated
outer cycle.  The first branch is the shorter conjugacy representative used
in Hull's proof.  The second branch is the long prime-piece alternative that
contradicts Hull's `C₁` bound. -/
structure Lemma49GreendlingerCertificate
    {G : Type u} [Group G] {Λ : Type w}
    {D : GGT.RelGenSet G Λ}
    {v : List (GGT.RelLetter G Λ)} {g : G} {n : ℕ}
    {eps : ℕ} {mu : ℝ}
    (N : Subgroup G)
    (Z : Lemma49GeodesicPowerDiagram D v g n)
    (B : Lemma49DesignatedBoundaryCycle D
      (RelWord.symmetrized v) Z.cells g n) where
  cell : Lemma44OrientedRelatorCell (RelWord.symmetrized v)
  cell_mem : cell ∈ Z.cells
  alternative :
    (∃ h : G,
      ConjugateModulo N g h ∧
        wordNorm D.alphabet.carrier h < wordNorm D.alphabet.carrier g) ∨
    (∃ u u' : List (GGT.RelLetter G Λ),
      RelWord.IsPrimePiece D (RelWord.symmetrized v) eps u u' cell.relator ∧
      ¬ max (u.length : ℝ) (u'.length : ℝ) <
        mu * (cell.relator.length : ℝ))

/-- The remaining relative Greendlinger estimate in the generality of a
reduced oriented diagram with a designated boundary cycle.  For every
nontrivial power, the selected cell either shortens the shortest
quotient-conjugacy representative or violates the prime-piece estimate.
This is the one-section estimating-graph conclusion in Hull's proof of
Lemma 4.9, with the input diagram and boundary cycle made explicit. -/
def HullLemma49GreendlingerEstimate : Prop :=
  ∀ {G : Type u} [Group G] {Λ : Type w}
    (D : GGT.RelGenSet G Λ),
    D.IsHyperbolicallyEmbedded →
    IsAcylindrical G (Cayley D.alphabet) →
      ∃ (eps rho : ℕ) (mu : ℝ), 0 < mu ∧
        ∀ (W : Set (List (GGT.RelLetter G Λ)))
          (v : List (GGT.RelLetter G Λ)), v ∈ W →
          RelWord.IsLemma49Input D W eps mu rho →
            ∀ (g : G) (n : ℕ),
              IsShortestModuloConjugacy D.alphabet.carrier
                (Subgroup.normalClosure
                  ({GGT.RelLetter.listVal v} : Set G)) g →
              ∀ (Z : Lemma49GeodesicPowerDiagram D v g n),
                ∀ (B : Lemma49DesignatedBoundaryCycle D
                  (RelWord.symmetrized v) Z.cells g n),
                  Z.power_ne_one →
                  Nonempty (Lemma49GreendlingerCertificate
                    (Subgroup.normalClosure
                      ({GGT.RelLetter.listVal v} : Set G)) Z B)

/-- A designated empty outer word spells the identity, so it cannot be the
nontrivial-power branch of the Greendlinger estimate. -/
theorem lemma49Greendlinger_emptyBoundary
    {G : Type u} [Group G] {Λ : Type w}
    {D : GGT.RelGenSet G Λ}
    {v : List (GGT.RelLetter G Λ)} {g : G} {n : ℕ}
    (Z : Lemma49GeodesicPowerDiagram D v g n)
    (B : Lemma49DesignatedBoundaryCycle D
      (RelWord.symmetrized v) Z.cells g n)
    (hword : B.word = []) :
    ¬ Z.power_ne_one := by
  intro hne
  have hval : GGT.RelLetter.listVal B.word = g := B.geodesic.2.1
  have hg : g = 1 := by
    rw [hword] at hval
    simpa using hval.symm
  exact hne (by simp [hg])

/-- A zero-exponent power is the identity in every group, so a reduced power
diagram with exponent zero cannot enter the nontrivial-power branch. -/
theorem lemma49Greendlinger_zeroExponent
    {G : Type u} [Group G] {Λ : Type w}
    {D : GGT.RelGenSet G Λ}
    {v : List (GGT.RelLetter G Λ)} {g : G}
    (Z : Lemma49GeodesicPowerDiagram D v g 0) :
    ¬ Z.power_ne_one := by
  intro hne
  exact hne (by simp)

/-- The Greendlinger estimate implies the shortest geodesic power-diagram
statement.  The first certificate branch contradicts shortestness.  The
second branch contradicts `primePiecesSmall` after restricting the input to
the symmetrized relator. -/
theorem hullLemma49ShortestGeodesicPowerDiagramStatement_of_greendlinger
    (hgeom : HullLemma49GreendlingerEstimate.{u, w}) :
    HullLemma49ShortestGeodesicPowerDiagramStatement.{u, w} := by
  intro G _ Λ D hemb hacy
  obtain ⟨eps, rho, mu, hmu, hgood⟩ := hgeom D hemb hacy
  refine ⟨eps, rho, mu, hmu, ?_⟩
  intro W v hv hinput g n hshort Z
  let N : Subgroup G :=
    Subgroup.normalClosure ({GGT.RelLetter.listVal v} : Set G)
  by_cases htrivial : g ^ n = 1
  · exact ⟨1, N.one_mem, by simpa using htrivial⟩
  · have hsym : RelWord.IsLemma49Input D
        (RelWord.symmetrized v) eps mu rho :=
      hinput.restrict_symmetrized hv
    let B : Lemma49DesignatedBoundaryCycle D
        (RelWord.symmetrized v) Z.cells g n :=
      { word := Z.boundaryWord
        geodesic := Z.boundary_geodesic
        cycle_value := Z.boundaryPower_value_eq_cells }
    obtain ⟨C⟩ := hgood W v hv hinput g n hshort Z B htrivial
    rcases C.alternative with hshorter | hprime
    · obtain ⟨h, hconj, hlt⟩ := hshorter
      have hnot : ¬ wordNorm D.alphabet.carrier h <
          wordNorm D.alphabet.carrier g :=
        Nat.not_lt_of_ge (hshort h hconj)
      exact (hnot hlt).elim
    · obtain ⟨u, u', hpiece, hnot⟩ := hprime
      have hsmall := hsym.primePiecesSmall u u' C.cell.relator hpiece
      exact (hnot hsmall).elim

/-- In the one-point group the estimate is model-tested by the empty
nontrivial-power branch: every group element is `1`, so the assumed
`power_ne_one` is impossible. -/
theorem hullLemma49GreendlingerEstimate_trivialModel
    {Λ : Type w} (D : GGT.RelGenSet PUnit Λ) :
    D.IsHyperbolicallyEmbedded →
    IsAcylindrical PUnit (Cayley D.alphabet) →
      ∃ (eps rho : ℕ) (mu : ℝ), 0 < mu ∧
        ∀ (W : Set (List (GGT.RelLetter PUnit Λ)))
          (v : List (GGT.RelLetter PUnit Λ)), v ∈ W →
          RelWord.IsLemma49Input D W eps mu rho →
            ∀ (g : PUnit) (n : ℕ),
              IsShortestModuloConjugacy D.alphabet.carrier
                (Subgroup.normalClosure
                  ({GGT.RelLetter.listVal v} : Set PUnit)) g →
              ∀ (Z : Lemma49GeodesicPowerDiagram D v g n),
                ∀ (B : Lemma49DesignatedBoundaryCycle D
                  (RelWord.symmetrized v) Z.cells g n),
                  Z.power_ne_one →
                  Nonempty (Lemma49GreendlingerCertificate
                    (Subgroup.normalClosure
                      ({GGT.RelLetter.listVal v} : Set PUnit)) Z B) := by
  intro _ _
  refine ⟨0, 0, 1, by norm_num, ?_⟩
  intro W v hv hinput g n hshort Z B hne
  exact (hne (Subsingleton.elim _ _)).elim

/-- The same empty-power check works in the two-point cyclic model, including
the identity element that tests the vacuous branch of the estimate. -/
theorem hullLemma49GreendlingerEstimate_twoPointModel
    {Λ : Type w} (D : GGT.RelGenSet (Multiplicative (ZMod 2)) Λ)
    {v : List (GGT.RelLetter (Multiplicative (ZMod 2)) Λ)}
    {Z : Lemma49GeodesicPowerDiagram D v
      (1 : Multiplicative (ZMod 2)) 0}
    : ¬ Z.power_ne_one := by
  exact lemma49Greendlinger_zeroExponent Z

/-- The free group on one generator has the same identity-power model check;
the nontrivial-generator case remains governed by the certificate alternative
in the preceding theorem. -/
theorem hullLemma49GreendlingerEstimate_freeGroupOneGeneratorModel
    {Λ : Type w} (D : GGT.RelGenSet (FreeGroup Unit) Λ)
    {v : List (GGT.RelLetter (FreeGroup Unit) Λ)}
    {Z : Lemma49GeodesicPowerDiagram D v (1 : FreeGroup Unit) 0}
    : ¬ Z.power_ne_one := by
  exact lemma49Greendlinger_zeroExponent Z

end HullSC
end GroupApproximation
