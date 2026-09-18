import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.FLLists
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Chain
import GroupApproximation.Meta.AxiomGuard

/-!
# Vertex balance of face-class colourings

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2`.  Lane gl-p10-54.

This module is the counting half of the lane.  For a combinatorial map `M`, a vertex `o` and a
predicate `p` on darts, `outN p o` counts the `p`-darts leaving `o` and `inN p o` the `p`-darts
arriving at `o` (a dart `x` arrives at the vertex of `alpha x`).  `p` is *balanced* when the two
agree at every vertex.

## The route

1. A `facePerm`-closed set is balanced: `facePerm = sigma * alpha` maps the darts arriving at `o`
   bijectively onto the darts leaving `o` (`roseLobeBlk_inN_eq_outN_of_facePerm`).
2. An `alpha`-closed set is balanced: `alpha` swaps arriving and leaving.
3. Let `z` be constant along `FaceClassStep M keep`.  Then `{z}` is `facePerm`-closed and
   `{z ∧ z ∘ alpha}` is `alpha`-closed, so their difference, the *boundary* `{z ∧ ¬ z ∘ alpha}`,
   is balanced (`roseLobeBlk_balanced_boundary`); so is the reversed boundary.
4. For lists, `outL L o` and `inL L o` count the darts of `L` leaving and arriving at `o`.  Along
   a dart chain the counts differ only at the two ends (`roseLobeBlk_chain_count`), so a nonempty
   chain with balanced counts is closed (`roseLobeBlk_closes`), and a closed dart walk has
   balanced counts (`roseLobeBlk_balanced_of_closed`).

No planarity is used: this is pure double counting.  `BlkBlock` applies it to the removed darts
of a lobe move to close up the block clause of `roseLobeFL_BlockStatement`.

## LOUD: strength

Everything here is proved; nothing is open in this module.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe

universe v

section Counts

variable {M : CombMap.{v}}

/-- The number of darts of a list leaving a vertex. -/
noncomputable def roseLobeBlk_outL (M : CombMap.{v}) (L : List M.Dart) (o : M.Vertex) : ℕ :=
  @List.countP M.Dart (fun x => @decide (M.vertexOf x = o) (Classical.propDecidable _)) L

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeBlk_outL

/-- The number of darts of a list arriving at a vertex. -/
noncomputable def roseLobeBlk_inL (M : CombMap.{v}) (L : List M.Dart) (o : M.Vertex) : ℕ :=
  @List.countP M.Dart
    (fun x => @decide (M.vertexOf (M.alpha x) = o) (Classical.propDecidable _)) L

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeBlk_inL

/-- The number of `p`-darts leaving a vertex. -/
noncomputable def roseLobeBlk_outN (M : CombMap.{v}) (p : M.Dart → Prop) (o : M.Vertex) : ℕ := by
  classical
  exact (Finset.univ.filter fun x => p x ∧ M.vertexOf x = o).card

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeBlk_outN

/-- The number of `p`-darts arriving at a vertex. -/
noncomputable def roseLobeBlk_inN (M : CombMap.{v}) (p : M.Dart → Prop) (o : M.Vertex) : ℕ := by
  classical
  exact (Finset.univ.filter fun x => p x ∧ M.vertexOf (M.alpha x) = o).card

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeBlk_inN

/-- A set of darts is balanced when at every vertex as many of its darts leave as arrive. -/
def roseLobeBlk_Balanced (M : CombMap.{v}) (p : M.Dart → Prop) : Prop :=
  ∀ o, roseLobeBlk_outN M p o = roseLobeBlk_inN M p o

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeBlk_Balanced

/-- A face step lands at the vertex where the dart arrives. -/
theorem roseLobeBlk_vertexOf_facePerm (x : M.Dart) :
    M.vertexOf (M.facePerm x) = M.vertexOf (M.alpha x) := by
  show M.vertexOf (M.sigma (M.alpha x)) = M.vertexOf (M.alpha x)
  exact M.vertexOf_sigma _

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeBlk_vertexOf_facePerm

/-- A `facePerm`-closed set is balanced at each vertex. -/
theorem roseLobeBlk_inN_eq_outN_of_facePerm {p : M.Dart → Prop}
    (hp : ∀ x, p (M.facePerm x) ↔ p x) (o : M.Vertex) :
    roseLobeBlk_inN M p o = roseLobeBlk_outN M p o := by
  classical
  unfold roseLobeBlk_inN roseLobeBlk_outN
  refine Finset.card_equiv M.facePerm fun x => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, hp, roseLobeBlk_vertexOf_facePerm]

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeBlk_inN_eq_outN_of_facePerm

/-- An `alpha`-closed set is balanced at each vertex. -/
theorem roseLobeBlk_inN_eq_outN_of_alpha {p : M.Dart → Prop}
    (hp : ∀ x, p (M.alpha x) ↔ p x) (o : M.Vertex) :
    roseLobeBlk_inN M p o = roseLobeBlk_outN M p o := by
  classical
  unfold roseLobeBlk_inN roseLobeBlk_outN
  refine Finset.card_equiv M.alpha fun x => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, hp]

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeBlk_inN_eq_outN_of_alpha
