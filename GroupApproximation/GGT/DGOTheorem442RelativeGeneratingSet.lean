import GroupApproximation.GGT.DGOTheorem442CosetGraphHyperbolic
import GroupApproximation.GGT.DGOTheorem442ProjectionSystem

/-!
# The relative generating set in DGO Theorem 4.42

For an equivariant projection system on `G/H`, use threshold `64 xi` and take
as base letters the elements carrying the identity coset across one projection
graph edge.  The preceding BBF standard-walk argument proves the associated
relative Cayley graph hyperbolic.
-/

namespace GroupApproximation
namespace GGT

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

variable {G : Type u} [Group G] {H : Subgroup G}

namespace EquivariantProjectionSystem

/-- The fixed threshold used for the DGO 4.42 projection graph. -/
def dgo442Threshold (P : EquivariantProjectionSystem G (G ⧸ H)) : ℝ :=
  64 * P.ξ

/-- The BBF projection graph at the DGO threshold. -/
noncomputable def dgo442Graph
    (P : EquivariantProjectionSystem G (G ⧸ H)) : SimpleGraph (G ⧸ H) :=
  (ProjectionPerturbation.bbf P.toProjectionSystem).graph P.dgo442Threshold

/-- Left translation preserves the DGO-threshold graph. -/
theorem dgo442Graph_adj_smul_iff
    (P : EquivariantProjectionSystem G (G ⧸ H))
    (g : G) (A B : G ⧸ H) :
    P.dgo442Graph.Adj (g • A) (g • B) ↔ P.dgo442Graph.Adj A B := by
  change
    ((EquivariantProjectionPerturbation.bbf P).toProjectionPerturbation.graph
      P.dgo442Threshold).Adj (g • A) (g • B) ↔
    ((EquivariantProjectionPerturbation.bbf P).toProjectionPerturbation.graph
      P.dgo442Threshold).Adj A B
  exact EquivariantProjectionPerturbation.graph_adj_smul_iff
    (EquivariantProjectionPerturbation.bbf P) P.dgo442Threshold g A B

/-- The DGO-threshold graph is preconnected. -/
theorem dgo442Graph_preconnected
    (P : EquivariantProjectionSystem G (G ⧸ H)) :
    P.dgo442Graph.Preconnected := by
  exact P.toProjectionSystem.bbf_graph_preconnected (by
    change 4 * P.ξ ≤ 64 * P.ξ
    linarith [P.ξ_pos])

/-- The edge-defined relative generating set at threshold `64 xi`. -/
noncomputable def dgo442RelGenSet
    (H : Subgroup G) (P : EquivariantProjectionSystem G (G ⧸ H)) :
    RelGenSet G Unit :=
  CosetGraph.relGenSet H P.dgo442Graph P.dgo442Graph_adj_smul_iff
    P.dgo442Graph_preconnected

@[simp] theorem dgo442RelGenSet_fam
    (H : Subgroup G) (P : EquivariantProjectionSystem G (G ⧸ H)) :
    (P.dgo442RelGenSet H).fam = fun _ => H :=
  rfl

@[simp] theorem dgo442RelGenSet_base
    (H : Subgroup G) (P : EquivariantProjectionSystem G (G ⧸ H)) :
    (P.dgo442RelGenSet H).base = CosetGraph.base H P.dgo442Graph :=
  rfl

/-- The relative Cayley graph of the DGO-threshold generating set is
hyperbolic. -/
theorem exists_dgo442RelGenSet_hyperbolic
    (H : Subgroup G) (P : EquivariantProjectionSystem G (G ⧸ H)) :
    ∃ delta : ℝ, IsHyperbolicSpace delta
      (Cayley (P.dgo442RelGenSet H).alphabet) := by
  have hK : 64 * P.ξ ≤ P.dgo442Threshold := le_rfl
  have hinv : ∀ (g : G) (A B : G ⧸ H),
      ((ProjectionPerturbation.bbf P.toProjectionSystem).graph
        P.dgo442Threshold).Adj (g • A) (g • B) ↔
      ((ProjectionPerturbation.bbf P.toProjectionSystem).graph
        P.dgo442Threshold).Adj A B := by
    exact P.dgo442Graph_adj_smul_iff
  obtain ⟨delta, hfour⟩ :=
    P.toProjectionSystem.exists_fourPoint_of_bbf_coset_graph hK hinv
  have hfour' : Hyperbolic.IsFourPointHyperbolic
      (P.dgo442RelGenSet H).alphabet.carrier delta := by
    simpa only [dgo442RelGenSet, dgo442Graph, CosetGraph.relGenSet,
      RelGenSet.alphabet] using hfour
  exact ⟨delta, isHyperbolicSpace_cayley_of_fourPoint _ hfour'⟩

/-- The DGO-threshold projection graph itself is hyperbolic in its graph
metric.  This is the specialization of BBF Theorem 3.16 used in DGO section
4.5. -/
theorem exists_dgo442Graph_hyperbolic
    (H : Subgroup G) (P : EquivariantProjectionSystem G (G ⧸ H)) :
    ∃ delta : ℝ, IsHyperbolicSpace delta
      (CosetGraph.Space P.dgo442Graph
        (CosetGraph.connected_of_preconnected H P.dgo442Graph
          P.dgo442Graph_preconnected)) := by
  obtain ⟨delta, hCayley⟩ := P.exists_dgo442RelGenSet_hyperbolic H
  refine ⟨delta + 3, ?_⟩
  simpa only [mul_one] using
    (isHyperbolicSpace_of_additiveDistortion
      (CosetGraph.representativeMap_additiveDistortion H P.dgo442Graph
        P.dgo442Graph_adj_smul_iff P.dgo442Graph_preconnected) hCayley)

end EquivariantProjectionSystem
end GGT
end GroupApproximation
