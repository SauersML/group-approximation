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

/-- **The cell bounds of Osin's condition on a diagram `X`**: `W` is closed under formal
inversion and rotation; every relator cell has at least `ρ` darts (long); every arc of `k`
darts of a relator cell has value of norm at least `λ k - c` (qg); every `ε`-piece is shorter
than `μ` times its word (pieces). -/
def roseLobeOsinCore_CellBounds {G : Type u} [Group G] {Lambda : Type w}
    (D : RelGenSet G Lambda) (W : Set (List (RelLetter G Lambda)))
    (X : DiscDiagram.{u, w, v} W) (eps : ℕ) (mu lambda c : ℝ) (rho : ℕ) : Prop :=
  (∀ word ∈ W, HullSC.RelWord.revInv word ∈ W) ∧
    (∀ word ∈ W, ∀ n : ℕ, word.rotate n ∈ W) ∧
    (∀ i : Fin X.rCellCount, rho ≤ (cellDarts X i).length) ∧
    (∀ (i : Fin X.rCellCount) (n k : ℕ), k ≤ (cellDarts X i).length →
      lambda * (k : ℝ) - c ≤ (WordMetric.wordNorm D.alphabet.carrier
        (RelLetter.listVal (((dartWord X (cellDarts X i)).rotate n).take k)) : ℝ)) ∧
    ∀ first word : List (RelLetter G Lambda), HullSC.RelWord.IsPiece D W eps first word →
      (first.length : ℝ) < mu * word.length

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeOsinCore_CellBounds

/-- `OsinCCondition` gives the cell bounds on every diagram over `W`. -/
theorem roseLobeOsinCore_cellBounds_of {G : Type u} [Group G] {Lambda : Type w}
    {D : RelGenSet G Lambda} {W : Set (List (RelLetter G Lambda))} {eps : ℕ}
    {mu lambda c : ℝ} {rho : ℕ} (hC : OsinCCondition D W eps mu lambda c rho)
    (X : DiscDiagram.{u, w, v} W) : roseLobeOsinCore_CellBounds D W X eps mu lambda c rho :=
  ⟨hC.inv_mem, hC.rotate_mem, roseLobeOsin_rho_le_cell hC X, roseLobeOsinCore_cell_qg hC X,
    hC.pieces_small⟩

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeOsinCore_cellBounds_of

/-- **A value-one arc of a relator cell is short**: `λ k ≤ c`. -/
theorem roseLobeOsinCore_mul_le_of_value_one {G : Type u} [Group G] {Lambda : Type w}
    {D : RelGenSet G Lambda} {W : Set (List (RelLetter G Lambda))} {eps : ℕ}
    {mu lambda c : ℝ} {rho : ℕ} {X : DiscDiagram.{u, w, v} W}
    (hB : roseLobeOsinCore_CellBounds D W X eps mu lambda c rho) (i : Fin X.rCellCount)
    (n k : ℕ) (hk : k ≤ (cellDarts X i).length)
    (h1 : RelLetter.listVal (((dartWord X (cellDarts X i)).rotate n).take k) = 1) :
    lambda * (k : ℝ) ≤ c := by
  obtain ⟨-, -, -, hqg, -⟩ := hB
  have h := hqg i n k hk
  rw [h1, WordMetric.wordNorm_one, Nat.cast_zero] at h
  linarith

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeOsinCore_mul_le_of_value_one

/-- A dart followed by its reverse spells a word of value `1`. -/
theorem roseLobeOsinCore_listVal_backtrack {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))} (X : DiscDiagram.{u, w, v} W)
    (d : X.toCombMap.Dart) :
    RelLetter.listVal [X.label d, X.label (X.toCombMap.alpha d)] = 1 := by
  rw [roseLobeOsinCore_listVal_cons, roseLobeOsinCore_listVal_cons, RelLetter.listVal_nil,
    mul_one, X.label_alpha, HullSC.RelWord.val_inv, mul_inv_cancel]

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeOsinCore_listVal_backtrack

/-- **A spike of a relator cell forces `2 λ ≤ c`.**  The spike is two consecutive darts `d`,
`α d` of the cell boundary, read here as the first two letters of a rotation of the cell word.
This is the configuration that the qg clause excludes in the truth check. -/
theorem roseLobeOsinCore_two_mul_le_of_spike {G : Type u} [Group G] {Lambda : Type w}
    {D : RelGenSet G Lambda} {W : Set (List (RelLetter G Lambda))} {eps : ℕ}
    {mu lambda c : ℝ} {rho : ℕ} {X : DiscDiagram.{u, w, v} W}
    (hB : roseLobeOsinCore_CellBounds D W X eps mu lambda c rho) (i : Fin X.rCellCount)
    (n : ℕ) (d : X.toCombMap.Dart) (hk : 2 ≤ (cellDarts X i).length)
    (hs : ((dartWord X (cellDarts X i)).rotate n).take 2 =
      [X.label d, X.label (X.toCombMap.alpha d)]) :
    lambda * 2 ≤ c := by
  have h := roseLobeOsinCore_mul_le_of_value_one hB i n 2 hk
    (by rw [hs]; exact roseLobeOsinCore_listVal_backtrack X d)
  exact_mod_cast h

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeOsinCore_two_mul_le_of_spike

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe
