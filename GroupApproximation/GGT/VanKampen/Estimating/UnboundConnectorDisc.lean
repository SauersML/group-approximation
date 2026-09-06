import GroupApproximation.GGT.VanKampen.NullWordDisc
import GroupApproximation.GGT.VanKampen.Estimating.UnboundWordConnectors

/-!
# A G-cell disc for the actual unbound connector quadrilateral

The source segment has positive length, so the constructed quadrilateral is
a nonempty null word. The explicit polygon filling gives an actual reduced
disc with one G-cell, no relator cells, and legal labels. This standalone
disc is the padding input; its insertion into a complementary region and
disjointness from the selected contiguities are still separate obligations.
-/

namespace GroupApproximation.GGT.VanKampen.UnboundEstimate.WordConnectorPair

open GroupApproximation.HullSC

universe u w
variable {G : Type u} [Group G] {Lambda : Type w}
  {D : RelGenSet G Lambda} {v : ℕ → G} {word : ℕ → List (RelLetter G Lambda)}
  {n eps : ℕ} {A B : Set ℕ} (C : WordConnectorPair D v word n A B eps)

theorem boundaryWord_ne_nil : C.boundaryWord ≠ [] := by
  have hlen : 0 < C.sourceWord.length := by
    rw [C.sourceWord_eq, List.length_take, List.length_drop]
    have := C.source_forward
    have := C.a'_le
    omega
  intro hnil
  have htotal := congrArg List.length hnil
  simp only [boundaryWord, List.length_append, List.length_nil] at htotal
  omega

/-- The metric pair's four words bound an explicitly constructed G-cell
disc. Its exact relative boundary, admissibility, and two-face count are
retained, with no ambient diagram supplied as an oracle. -/
theorem exists_gCellDisc (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base)
    (W : Set (List (RelLetter G Lambda))) :
    ∃ Delta : DiscDiagram.{u, w, 0} W,
      Delta.boundaryWord = C.boundaryWord ∧ Delta.relatorCells = [] ∧ Delta.Reduced ∧
        (∀ d : Delta.toCombMap.Dart, D.IsLetter (Delta.label d)) ∧
        Delta.toCombMap.faceCount = 2 :=
  nullWordDisc G Lambda D hsymm C.boundaryWord (C.boundaryWord_admissible hsymm)
    C.boundaryWord_ne_nil C.boundaryWord_value W

end GroupApproximation.GGT.VanKampen.UnboundEstimate.WordConnectorPair

#audit_axioms GroupApproximation.GGT.VanKampen.UnboundEstimate.WordConnectorPair.boundaryWord_ne_nil
#audit_axioms GroupApproximation.GGT.VanKampen.UnboundEstimate.WordConnectorPair.exists_gCellDisc
