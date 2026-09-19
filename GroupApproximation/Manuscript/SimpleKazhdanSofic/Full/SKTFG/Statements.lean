import GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.FullGroup
import GroupApproximation.Manuscript.SimpleKazhdanSofic.WordProblemDegreeStatements
import GroupApproximation.Meta.AxiomGuard

/-!
# Derived topological full groups: the two attribution rows of `simple_kazhdan_sofic_group.tex`

Two census rows credit results about derived topological full groups. The manuscript's argument
does not use either result; each is the analogue, for `[[T]]'`, of a theorem the paper proves for
its groups `G_X`.

* Row `3eaee0a2dc7e` (tex l.307–309): "For derived topological full groups, Matui showed by a
  similar argument that a nontrivial normal subgroup meets a simple union of products of
  alternating groups on towers [Matui, Lemma 3.4 and Theorem 4.9]." The conclusion Matui draws is
  Theorem 4.9: `[[T]]'` is simple for every Cantor minimal system. It is stated here as
  `MatuiDerivedFullGroupSimpleStatement`.
* Row `e5932a45f053` (tex l.724–726): "For derived topological full groups, Grigorchuk and Medynets
  proved that the word problem is solvable if and only if `L(X)` is recursive [GMpres,
  Thm 1.1(3)]." It is stated here as `GrigorchukMedynetsWordProblemStatement`, with the finite
  generation of `[[σ_X]]'` (Matui) built into the statement.

Both are named propositions. Neither is proved here, so neither row is regraded. The plan for the
proofs, which builds on the tower permutations of `FlipConverse.InfraTowerPerm*`, is on the lane
board `sk-tfg`. What this file proves is the definition of `[[T]]'` and the inclusion
`[[T]]' ≤ [[T]]`.
-/

namespace GroupApproximation.Full.SKTFG

open GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse
open SymbolicDynamics.FullShift

universe u

section Derived

variable {X : Type*} [TopologicalSpace X]

/-- The derived topological full group `[[T]]'`, the commutator subgroup of `[[T]]`, as a subgroup
of the homeomorphism group of `X`. -/
def derivedFullGroup (T : X ≃ₜ X) : Subgroup (X ≃ₜ X) :=
  ⁅topologicalFullGroup T, topologicalFullGroup T⁆

/-- `[[T]]' ≤ [[T]]`: a commutator `g h g⁻¹ h⁻¹` of elements of `[[T]]` lies in `[[T]]`. -/
theorem derivedFullGroup_le (T : X ≃ₜ X) : derivedFullGroup T ≤ topologicalFullGroup T := by
  refine Subgroup.commutator_le.mpr fun g hg h hh => ?_
  rw [commutatorElement_def]
  exact (topologicalFullGroup T).mul_mem
    ((topologicalFullGroup T).mul_mem ((topologicalFullGroup T).mul_mem hg hh)
      ((topologicalFullGroup T).inv_mem hg))
    ((topologicalFullGroup T).inv_mem hh)

#audit_axioms derivedFullGroup_le

/-- A Cantor minimal system: `X` is a nonempty compact metrizable totally disconnected perfect
space, which makes it homeomorphic to the Cantor set, and every `T`-orbit is dense. -/
def IsCantorMinimal (T : X ≃ₜ X) : Prop :=
  CompactSpace X ∧ TopologicalSpace.MetrizableSpace X ∧ TotallyDisconnectedSpace X ∧
    PerfectSpace X ∧ Nonempty X ∧ IsMinimalHomeo T

end Derived

/-- **Matui, Theorem 4.9** (row `3eaee0a2dc7e`, tex l.307–309). For every Cantor minimal system
`(X, T)`, the derived topological full group `[[T]]'` is simple. Matui's Lemma 3.4 is the step
the tex sentence describes: a nontrivial normal subgroup meets the simple union of the products of
alternating groups on the towers of a refining sequence of Kakutani–Rokhlin partitions. -/
def MatuiDerivedFullGroupSimpleStatement : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] (T : X ≃ₜ X), IsCantorMinimal T →
    IsSimpleGroup ↥(derivedFullGroup T)

/-- **Grigorchuk–Medynets, Theorem 1.1(3)** (row `e5932a45f053`, tex l.724–726), with Matui's
finite generation of `[[σ_X]]'` for minimal subshifts. For an infinite minimal subshift `X` over a
finite alphabet, `[[σ_X]]'` has a finite generating family whose word problem is solvable if and
only if the language `L(X)` is recursive. This uses the oracles `wordProblemOracle` and
`languageOracle` of the paper's own `cor:wp` (`Full.SK13.wp_solvable_iff_recursive`). -/
def GrigorchukMedynetsWordProblemStatement : Prop :=
  ∀ (A : Type) [TopologicalSpace A] [DiscreteTopology A] [Fintype A] [DecidableEq A]
    [Primcodable A] (S : Subshift A ℤ), Infinite S.carrier →
    GroupApproximation.SimpleKazhdanSofic.IsMinimal S →
    ∃ (k : ℕ) (s : Fin k → ↥(derivedFullGroup (GroupApproximation.SimpleKazhdanSofic.subshiftHomeo S))),
      Subgroup.closure (Set.range s) = ⊤ ∧
      (Partrec (GroupApproximation.SimpleKazhdanSofic.wordProblemOracle s) ↔
        Partrec (GroupApproximation.SimpleKazhdanSofic.languageOracle S))

end GroupApproximation.Full.SKTFG
