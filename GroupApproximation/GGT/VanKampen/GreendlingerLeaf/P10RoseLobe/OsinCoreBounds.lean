import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.OsinStatement
import GroupApproximation.Meta.AxiomGuard

/-!
# The cell bounds that `OsinCCondition` puts on a diagram

Lane gl-p10-76.  Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).

`roseLobeOsin_RegionStatement` assumes `OsinCCondition D W ε μ λ c ρ`, a condition on the
family `W`.  A pocket argument only reads it through the relator cells of `X`.  This module
states those consequences, `roseLobeOsinCore_CellBounds D W X ε μ λ c ρ`, and proves them from
`OsinCCondition` (`roseLobeOsinCore_cellBounds_of`).  There are five of them.

* `W` is closed under formal inversion and cyclic permutation (the fields `inv_mem`,
  `rotate_mem`).
* **long**: every relator cell has at least `ρ` darts (`roseLobeOsin_rho_le_cell`).
* **qg**: for every relator cell `i`, every rotation `n` and every `k ≤ |cell i|`,
  `λ k - c ≤ |listVal (take k (rotate n (word of cell i)))|`.
* **pieces**: the field `pieces_small` itself.

## Proof of qg

Let `v = rotate n (word of cell i)`.  Then `v ∈ W` by `rotate_mem`, and `|v| = |cell i|`.  The
quasi-geodesic clause at `i = 0`, `j = k` gives
`λ (k - 0) - c ≤ d(vertex 1 v 0, vertex 1 v k)`.  Here `vertex 1 v 0 = 1`,
`d(1, g) = |g|`, and `vertex a v k = a · listVal (take k v)`
(`roseLobeOsinCore_vertex_eq`, by induction on `v`).

## The local configuration the truth check isolates

A **spike** of a relator cell is two consecutive darts `d`, `α d` of its boundary (the boundary
runs out along an edge and straight back).  They spell `[ℓ d, (ℓ d)⁻¹]`, of value `1`
(`roseLobeOsinCore_listVal_backtrack`).  qg with value `1` gives `λ k ≤ c`
(`roseLobeOsinCore_mul_le_of_value_one`).  So a spike forces `2 λ ≤ c`
(`roseLobeOsinCore_two_mul_le_of_spike`), and any value-one arc, such as a tree of spikes, has
at most `c / λ` darts.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe

universe u w v

open Embedded

/-- The value of a word with its first letter split off. -/
theorem roseLobeOsinCore_listVal_cons {G : Type u} [Group G] {Lambda : Type w}
    (a : RelLetter G Lambda) (t : List (RelLetter G Lambda)) :
    RelLetter.listVal (a :: t) = a.val * RelLetter.listVal t := by
  simp only [RelLetter.listVal, List.map_cons, List.prod_cons]

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeOsinCore_listVal_cons

/-- Osin's vertex after `k` letters is the base point times the value of the prefix. -/
theorem roseLobeOsinCore_vertex_eq {G : Type u} [Group G] {Lambda : Type w} :
    ∀ (word : List (RelLetter G Lambda)) (a : G) (k : ℕ),
      OsinComponents.vertex a word k = a * RelLetter.listVal (word.take k)
  | [], a, k => by
      rw [OsinComponents.vertex_nil, List.take_nil, RelLetter.listVal_nil, mul_one]
  | _ :: _, a, 0 => by
      rw [OsinComponents.vertex_zero, List.take_zero, RelLetter.listVal_nil, mul_one]
  | b :: t, a, k + 1 => by
      rw [OsinComponents.vertex_cons_succ, roseLobeOsinCore_vertex_eq t, List.take_succ_cons,
        roseLobeOsinCore_listVal_cons, mul_assoc]

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeOsinCore_vertex_eq

/-- **The quasi-geodesic clause on a relator cell.**  Every arc of `k` darts of a relator cell
(any rotation) has value of norm at least `λ k - c`. -/
theorem roseLobeOsinCore_cell_qg {G : Type u} [Group G] {Lambda : Type w}
    {D : RelGenSet G Lambda} {W : Set (List (RelLetter G Lambda))} {eps : ℕ}
    {mu lambda c : ℝ} {rho : ℕ} (hC : OsinCCondition D W eps mu lambda c rho)
    (X : DiscDiagram.{u, w, v} W) (i : Fin X.rCellCount) (n k : ℕ)
    (hk : k ≤ (cellDarts X i).length) :
    lambda * (k : ℝ) - c ≤ (WordMetric.wordNorm D.alphabet.carrier
      (RelLetter.listVal (((dartWord X (cellDarts X i)).rotate n).take k)) : ℝ) := by
  have hmem : (dartWord X (cellDarts X i)).rotate n ∈ W := by
    rw [dartWord_cellDarts]
    exact hC.rotate_mem _ (cell X i).word_mem n
  have hlen : k ≤ ((dartWord X (cellDarts X i)).rotate n).length := by
    rw [List.length_rotate]
    simpa only [dartWord, List.length_map] using hk
  have h := (hC.quasiGeodesic _ hmem).2 0 k (Nat.zero_le k) hlen
  rw [OsinComponents.vertex_zero, WordMetric.wordDist_one_left, roseLobeOsinCore_vertex_eq,
    one_mul, Nat.sub_zero] at h
  exact h

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeOsinCore_cell_qg
