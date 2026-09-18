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

/-- Splitting the leaving count along a second predicate. -/
theorem roseLobeBlk_outN_split (p q : M.Dart → Prop) (o : M.Vertex) :
    roseLobeBlk_outN M p o =
      roseLobeBlk_outN M (fun x => p x ∧ q x) o + roseLobeBlk_outN M (fun x => p x ∧ ¬ q x) o := by
  classical
  unfold roseLobeBlk_outN
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext x
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  · rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hx'
    exact hx'.1.2 hx.1.2

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeBlk_outN_split

/-- Splitting the arriving count along a second predicate. -/
theorem roseLobeBlk_inN_split (p q : M.Dart → Prop) (o : M.Vertex) :
    roseLobeBlk_inN M p o =
      roseLobeBlk_inN M (fun x => p x ∧ q x) o + roseLobeBlk_inN M (fun x => p x ∧ ¬ q x) o := by
  classical
  unfold roseLobeBlk_inN
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext x
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  · rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hx'
    exact hx'.1.2 hx.1.2

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeBlk_inN_split

/-- Balance only depends on the predicate up to pointwise equivalence. -/
theorem roseLobeBlk_balanced_congr {p q : M.Dart → Prop} (hp : roseLobeBlk_Balanced M p)
    (hpq : ∀ x, p x ↔ q x) : roseLobeBlk_Balanced M q := by
  have h : p = q := funext fun x => propext (hpq x)
  subst h
  exact hp

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeBlk_balanced_congr

/-- **The boundary of a face-class colouring is balanced.**  If `z` is constant along the
face-class steps, the darts coloured `true` whose reverse is coloured `false` leave each vertex
as often as they arrive. -/
theorem roseLobeBlk_balanced_boundary {keep : M.Dart → Prop} {z : M.Dart → Bool}
    (hz : ∀ x y, CombMap.FaceClassStep M keep x y → z x = z y) :
    roseLobeBlk_Balanced M fun x => z x = true ∧ ¬ z (M.alpha x) = true := by
  intro o
  have hT : roseLobeBlk_inN M (fun x => z x = true) o =
      roseLobeBlk_outN M (fun x => z x = true) o :=
    roseLobeBlk_inN_eq_outN_of_facePerm (fun x => by
      show z (M.facePerm x) = true ↔ z x = true
      rw [← hz x (M.facePerm x) (Or.inl rfl)]) o
  have hQ : roseLobeBlk_inN M (fun x => z x = true ∧ z (M.alpha x) = true) o =
      roseLobeBlk_outN M (fun x => z x = true ∧ z (M.alpha x) = true) o :=
    roseLobeBlk_inN_eq_outN_of_alpha (fun x => by
      show z (M.alpha x) = true ∧ z (M.alpha (M.alpha x)) = true ↔
        z x = true ∧ z (M.alpha x) = true
      rw [M.alpha_involutive x]
      exact And.comm) o
  have h1 : roseLobeBlk_outN M (fun x => z x = true) o =
      roseLobeBlk_outN M (fun x => z x = true ∧ z (M.alpha x) = true) o +
        roseLobeBlk_outN M (fun x => z x = true ∧ ¬ z (M.alpha x) = true) o :=
    roseLobeBlk_outN_split _ _ o
  have h2 : roseLobeBlk_inN M (fun x => z x = true) o =
      roseLobeBlk_inN M (fun x => z x = true ∧ z (M.alpha x) = true) o +
        roseLobeBlk_inN M (fun x => z x = true ∧ ¬ z (M.alpha x) = true) o :=
    roseLobeBlk_inN_split _ _ o
  omega

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeBlk_balanced_boundary

/-- **The reversed boundary of a face-class colouring is balanced**: the darts coloured `false`
whose reverse is coloured `true`. -/
theorem roseLobeBlk_balanced_boundary_rev {keep : M.Dart → Prop} {z : M.Dart → Bool}
    (hz : ∀ x y, CombMap.FaceClassStep M keep x y → z x = z y) :
    roseLobeBlk_Balanced M fun x => z x = false ∧ z (M.alpha x) = true := by
  refine roseLobeBlk_balanced_congr (roseLobeBlk_balanced_boundary (keep := keep)
    (z := fun x => !z x) fun x y h => congrArg (fun b => !b) (hz x y h)) fun x => ?_
  show (!z x) = true ∧ ¬ (!z (M.alpha x)) = true ↔ z x = false ∧ z (M.alpha x) = true
  cases z x <;> cases z (M.alpha x) <;> simp

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeBlk_balanced_boundary_rev

theorem roseLobeBlk_outL_append (L L' : List M.Dart) (o : M.Vertex) :
    roseLobeBlk_outL M (L ++ L') o = roseLobeBlk_outL M L o + roseLobeBlk_outL M L' o := by
  unfold roseLobeBlk_outL
  exact List.countP_append

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeBlk_outL_append

theorem roseLobeBlk_inL_append (L L' : List M.Dart) (o : M.Vertex) :
    roseLobeBlk_inL M (L ++ L') o = roseLobeBlk_inL M L o + roseLobeBlk_inL M L' o := by
  unfold roseLobeBlk_inL
  exact List.countP_append

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeBlk_inL_append

theorem roseLobeBlk_outL_cons (x : M.Dart) (L : List M.Dart) (o : M.Vertex) :
    roseLobeBlk_outL M (x :: L) o = roseLobeBlk_outL M [x] o + roseLobeBlk_outL M L o := by
  unfold roseLobeBlk_outL
  rw [List.countP_cons (l := L), List.countP_singleton]
  exact Nat.add_comm _ _

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeBlk_outL_cons

theorem roseLobeBlk_inL_cons (x : M.Dart) (L : List M.Dart) (o : M.Vertex) :
    roseLobeBlk_inL M (x :: L) o = roseLobeBlk_inL M [x] o + roseLobeBlk_inL M L o := by
  unfold roseLobeBlk_inL
  rw [List.countP_cons (l := L), List.countP_singleton]
  exact Nat.add_comm _ _

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeBlk_inL_cons

/-- One chain step: a dart arrives where the next one leaves. -/
theorem roseLobeBlk_inL_singleton_eq_outL {a b : M.Dart}
    (h : M.vertexOf (M.alpha a) = M.vertexOf b) (o : M.Vertex) :
    roseLobeBlk_inL M [a] o = roseLobeBlk_outL M [b] o := by
  unfold roseLobeBlk_inL roseLobeBlk_outL
  rw [List.countP_singleton, List.countP_singleton, h]

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeBlk_inL_singleton_eq_outL

theorem roseLobeBlk_outL_singleton_self (x : M.Dart) :
    roseLobeBlk_outL M [x] (M.vertexOf x) = 1 := by
  simp [roseLobeBlk_outL]

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeBlk_outL_singleton_self

theorem roseLobeBlk_eq_of_inL_singleton {y : M.Dart} {o : M.Vertex}
    (h : roseLobeBlk_inL M [y] o = 1) : M.vertexOf (M.alpha y) = o := by
  by_contra hne
  simp [roseLobeBlk_inL, hne] at h

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeBlk_eq_of_inL_singleton

/-- **Counting along a dart chain**: arrivals plus the first departure equal departures plus the
last arrival. -/
theorem roseLobeBlk_chain_count (o : M.Vertex) (x : M.Dart) (t : List M.Dart)
    (hch : (x :: t).IsChain fun d e => M.vertexOf (M.alpha d) = M.vertexOf e) :
    roseLobeBlk_inL M (x :: t) o + roseLobeBlk_outL M [x] o =
      roseLobeBlk_outL M (x :: t) o +
        roseLobeBlk_inL M [(x :: t).getLast (List.cons_ne_nil x t)] o := by
  induction t generalizing x with
  | nil => exact Nat.add_comm _ _
  | cons y t ih =>
    rw [List.isChain_cons_cons] at hch
    have hs := roseLobeBlk_inL_singleton_eq_outL hch.1 o
    have hi := ih y hch.2
    have hl : (x :: y :: t).getLast (List.cons_ne_nil x (y :: t)) =
        (y :: t).getLast (List.cons_ne_nil y t) := rfl
    rw [hl, roseLobeBlk_inL_cons x (y :: t), roseLobeBlk_outL_cons x (y :: t)]
    omega

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeBlk_chain_count

/-- **A balanced dart chain closes up.** -/
theorem roseLobeBlk_closes {L : List M.Dart} (hne : L ≠ [])
    (hch : L.IsChain fun d e => M.vertexOf (M.alpha d) = M.vertexOf e)
    (hbal : ∀ o, roseLobeBlk_outL M L o = roseLobeBlk_inL M L o) : IsClosedDartWalk M L := by
  obtain ⟨x, t, rfl⟩ := List.exists_cons_of_ne_nil hne
  refine ⟨hne, hch, ?_⟩
  show M.vertexOf (M.alpha ((x :: t).getLast (List.cons_ne_nil x t))) = M.vertexOf x
  have h1 := roseLobeBlk_chain_count (M.vertexOf x) x t hch
  have h2 := hbal (M.vertexOf x)
  have h3 := roseLobeBlk_outL_singleton_self (M := M) x
  have h4 : roseLobeBlk_inL M [(x :: t).getLast (List.cons_ne_nil x t)] (M.vertexOf x) = 1 := by
    omega
  exact roseLobeBlk_eq_of_inL_singleton h4

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeBlk_closes

/-- **A closed dart walk is balanced.** -/
theorem roseLobeBlk_balanced_of_closed {L : List M.Dart} (hw : IsClosedDartWalk M L)
    (o : M.Vertex) : roseLobeBlk_outL M L o = roseLobeBlk_inL M L o := by
  obtain ⟨hne, hch, hcl⟩ := hw
  obtain ⟨x, t, rfl⟩ := List.exists_cons_of_ne_nil hne
  have hcl' : M.vertexOf (M.alpha ((x :: t).getLast (List.cons_ne_nil x t))) =
      M.vertexOf x := hcl
  have h1 := roseLobeBlk_chain_count o x t hch
  have h2 := roseLobeBlk_inL_singleton_eq_outL hcl' o
  omega

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeBlk_balanced_of_closed

/-- The leaving count of a duplicate-free list is that of its set of darts. -/
theorem roseLobeBlk_outL_eq_outN {L : List M.Dart} (hL : L.Nodup) {p : M.Dart → Prop}
    (hp : ∀ x, x ∈ L ↔ p x) (o : M.Vertex) :
    roseLobeBlk_outL M L o = roseLobeBlk_outN M p o := by
  classical
  unfold roseLobeBlk_outL roseLobeBlk_outN
  rw [List.countP_eq_length_filter, ← List.toFinset_card_of_nodup (hL.filter _)]
  congr 1
  ext x
  simp only [List.mem_toFinset, List.mem_filter, Finset.mem_filter, Finset.mem_univ, true_and,
    decide_eq_true_eq, hp]

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeBlk_outL_eq_outN

/-- The arriving count of a duplicate-free list is that of its set of darts. -/
theorem roseLobeBlk_inL_eq_inN {L : List M.Dart} (hL : L.Nodup) {p : M.Dart → Prop}
    (hp : ∀ x, x ∈ L ↔ p x) (o : M.Vertex) :
    roseLobeBlk_inL M L o = roseLobeBlk_inN M p o := by
  classical
  unfold roseLobeBlk_inL roseLobeBlk_inN
  rw [List.countP_eq_length_filter, ← List.toFinset_card_of_nodup (hL.filter _)]
  congr 1
  ext x
  simp only [List.mem_toFinset, List.mem_filter, Finset.mem_filter, Finset.mem_univ, true_and,
    decide_eq_true_eq, hp]

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeBlk_inL_eq_inN

/-- A duplicate-free nonempty dart chain whose set of darts is balanced closes up. -/
theorem roseLobeBlk_closes_of_balanced {L : List M.Dart} (hne : L ≠ []) (hL : L.Nodup)
    (hch : L.IsChain fun d e => M.vertexOf (M.alpha d) = M.vertexOf e) {p : M.Dart → Prop}
    (hbal : roseLobeBlk_Balanced M p) (hp : ∀ x, x ∈ L ↔ p x) : IsClosedDartWalk M L :=
  roseLobeBlk_closes hne hch fun o => by
    rw [roseLobeBlk_outL_eq_outN hL hp, roseLobeBlk_inL_eq_inN hL hp]
    exact hbal o

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeBlk_closes_of_balanced

end Counts

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe
