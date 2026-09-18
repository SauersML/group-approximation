import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseEndpoint.SingleRegion
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.ZMod.Defs
import GroupApproximation.Meta.AxiomGuard

/-!
# A parity count at a vertex: a lone removed run of a region move is closed

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-25.  Generic combinatorial
map lemmas, no open Statement.

Let `c` be the boundary cycle of a face set, `z` a colouring constant along the face-class steps
of the plane cut along `c` (for instance `regionColour M (walkKeep M c) r`), never colouring both
sides of a dart of `c`.  A dart `d` of `c` is *kept* when neither side is coloured
(`movePred M z d = true`) and *removed* otherwise.

* `extremalArcEndExists_parity_univ`: for a vertex-constant weight `δ`,
  `∑ x, δ x * (col (z x) + col (z (α x))) = 0` in `ZMod 2`, since `z (σ x) = z (α x)` (a face
  step) and `σ` permutes the darts.
* `extremalArcEndExists_parity`: the same sum restricted to the cycle, each dart counted with
  both of its ends, vanishes; off the cycle `x` and `α x` lie in one class.
* `extremalArcEndExists_telescope`: along a walk segment the ends telescope.
* `extremalArcEndExists_closed_run`: if every dart of `c` outside the gap between two kept darts
  `d` and `e` is kept and every dart of the gap is removed, then `α d` and `e` share a vertex.
  Counting at the vertex of `e`: the only nonzero terms are the removed darts, and they
  telescope to `[α d at w] + [e at w]`.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

universe v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove

/-- The class of a Boolean in `ZMod 2`. -/
def extremalArcEndExists_col : Bool → ZMod 2
  | true => 1
  | false => 0

/-- The indicator in `ZMod 2` of the darts at the vertex `w`. -/
noncomputable def extremalArcEndExists_at (M : CombMap.{v}) (w : M.Vertex) (x : M.Dart) :
    ZMod 2 :=
  @ite (ZMod 2) (M.vertexOf x = w) (Classical.propDecidable _) 1 0

/-- The parity term of a dart. -/
def extremalArcEndExists_term (M : CombMap.{v}) (z : M.Dart → Bool) (δ : M.Dart → ZMod 2)
    (x : M.Dart) : ZMod 2 :=
  δ x * (extremalArcEndExists_col (z x) + extremalArcEndExists_col (z (M.alpha x)))

/-- The parity weight of an edge, counted at both ends. -/
def extremalArcEndExists_weight (M : CombMap.{v}) (z : M.Dart → Bool) (δ : M.Dart → ZMod 2)
    (x : M.Dart) : ZMod 2 :=
  (δ x + δ (M.alpha x)) *
    (extremalArcEndExists_col (z x) + extremalArcEndExists_col (z (M.alpha x)))

theorem extremalArcEndExists_add_self : ∀ a : ZMod 2, a + a = 0 := by decide

theorem extremalArcEndExists_add_cancel : ∀ a b c : ZMod 2, a + b + (b + c) = a + c := by
  decide

theorem extremalArcEndExists_eq_one_of_add_one : ∀ a : ZMod 2, a + 1 = 0 → a = 1 := by
  decide

theorem extremalArcEndExists_col_removed {a b : Bool} (h : (!a && !b) = false)
    (h' : a = false ∨ b = false) :
    extremalArcEndExists_col a + extremalArcEndExists_col b = 1 := by
  revert h h'
  cases a <;> cases b <;> decide

theorem extremalArcEndExists_at_eq_one (M : CombMap.{v}) {w : M.Vertex} {x : M.Dart}
    (h : M.vertexOf x = w) : extremalArcEndExists_at M w x = 1 := by
  unfold extremalArcEndExists_at
  exact if_pos h

theorem extremalArcEndExists_at_eq_zero (M : CombMap.{v}) {w : M.Vertex} {x : M.Dart}
    (h : ¬M.vertexOf x = w) : extremalArcEndExists_at M w x = 0 := by
  unfold extremalArcEndExists_at
  exact if_neg h

theorem extremalArcEndExists_vertexOf_of_at (M : CombMap.{v}) {w : M.Vertex} {x : M.Dart}
    (h : extremalArcEndExists_at M w x = 1) : M.vertexOf x = w := by
  by_contra hne
  rw [extremalArcEndExists_at_eq_zero M hne] at h
  exact absurd h (by decide)

theorem extremalArcEndExists_at_congr (M : CombMap.{v}) (w : M.Vertex) {x y : M.Dart}
    (h : M.vertexOf x = M.vertexOf y) :
    extremalArcEndExists_at M w x = extremalArcEndExists_at M w y := by
  unfold extremalArcEndExists_at
  rw [h]

theorem extremalArcEndExists_at_sigma (M : CombMap.{v}) (w : M.Vertex) (x : M.Dart) :
    extremalArcEndExists_at M w (M.sigma x) = extremalArcEndExists_at M w x :=
  extremalArcEndExists_at_congr M w (CombMap.vertexOf_sigma M x)

/-- Two ends of an edge, counted together. -/
theorem extremalArcEndExists_term_add_alpha (M : CombMap.{v}) (z : M.Dart → Bool)
    (δ : M.Dart → ZMod 2) (x : M.Dart) :
    extremalArcEndExists_term M z δ x + extremalArcEndExists_term M z δ (M.alpha x) =
      extremalArcEndExists_weight M z δ x := by
  unfold extremalArcEndExists_term extremalArcEndExists_weight
  rw [M.alpha_involutive x,
    add_comm (extremalArcEndExists_col (z (M.alpha x))) (extremalArcEndExists_col (z x)),
    ← add_mul]

/-- A list sum of zero terms is zero. -/
theorem extremalArcEndExists_sum_map_eq_zero {α : Type*} (f : α → ZMod 2) (l : List α)
    (h : ∀ x ∈ l, f x = 0) : (l.map f).sum = 0 := by
  induction l with
  | nil => rw [List.map_nil, List.sum_nil]
  | cons x l ih =>
    rw [List.map_cons, List.sum_cons, h x (List.mem_cons.mpr (Or.inl rfl)),
      ih fun y hy => h y (List.mem_cons.mpr (Or.inr hy)), add_zero]

/-- List sums of termwise equal maps agree. -/
theorem extremalArcEndExists_sum_map_congr {α : Type*} (f g : α → ZMod 2) (l : List α)
    (h : ∀ x ∈ l, f x = g x) : (l.map f).sum = (l.map g).sum := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons,
      h x (List.mem_cons.mpr (Or.inl rfl)), ih fun y hy => h y (List.mem_cons.mpr (Or.inr hy))]

/-- **The parity count over all darts**: for a colouring constant along the face steps and a
vertex-constant weight, `∑ x, δ x * (col (z x) + col (z (α x))) = 0`. -/
theorem extremalArcEndExists_parity_univ (M : CombMap.{v}) (keep : M.Dart → Prop)
    (z : M.Dart → Bool) (hz : ∀ x y, CombMap.FaceClassStep M keep x y → z x = z y)
    (δ : M.Dart → ZMod 2) (hδ : ∀ x, δ (M.sigma x) = δ x) :
    ∑ x, extremalArcEndExists_term M z δ x = 0 := by
  have hs : ∀ x, z (M.alpha x) = z (M.sigma x) := fun x =>
    hz (M.alpha x) (M.sigma x) (Or.inl (by
      unfold CombMap.facePerm
      rw [Equiv.Perm.mul_apply, M.alpha_involutive x]))
  have hshift : ∑ x, δ x * extremalArcEndExists_col (z (M.alpha x)) =
      ∑ x, δ x * extremalArcEndExists_col (z x) :=
    calc ∑ x, δ x * extremalArcEndExists_col (z (M.alpha x))
        = ∑ x, δ (M.sigma x) * extremalArcEndExists_col (z (M.sigma x)) :=
          Finset.sum_congr rfl fun x _ => by rw [hδ x, hs x]
      _ = ∑ x, δ x * extremalArcEndExists_col (z x) :=
          Equiv.sum_comp M.sigma (fun y => δ y * extremalArcEndExists_col (z y))
  calc ∑ x, extremalArcEndExists_term M z δ x
      = ∑ x, δ x * extremalArcEndExists_col (z x) +
          ∑ x, δ x * extremalArcEndExists_col (z (M.alpha x)) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun x _ => mul_add _ _ _
    _ = ∑ x, δ x * extremalArcEndExists_col (z x) +
          ∑ x, δ x * extremalArcEndExists_col (z x) := by rw [hshift]
    _ = 0 := extremalArcEndExists_add_self _

/-- **The parity count on a boundary cycle**: with the cut along `c`, the edge weights of the
darts of `c` sum to zero. -/
theorem extremalArcEndExists_parity (M : CombMap.{v}) {faces : Finset M.Face}
    {c : List M.Dart} (hc : ∀ d, d ∈ c ↔ Surgery.MapCollapse.IsBoundaryDart M faces d)
    (hnd : c.Nodup) (z : M.Dart → Bool)
    (hz : ∀ x y, CombMap.FaceClassStep M (walkKeep M c) x y → z x = z y)
    (δ : M.Dart → ZMod 2) (hδ : ∀ x, δ (M.sigma x) = δ x) :
    (c.map (extremalArcEndExists_weight M z δ)).sum = 0 := by
  classical
  have hsum := extremalArcEndExists_parity_univ M (walkKeep M c) z hz δ hδ
  have hoff : ∀ x, x ∉ c → M.alpha x ∉ c → extremalArcEndExists_term M z δ x = 0 := by
    intro x hx hax
    unfold extremalArcEndExists_term
    rw [hz x (M.alpha x) (Or.inr ⟨fun h => Or.elim h hx hax, rfl⟩),
      extremalArcEndExists_add_self (extremalArcEndExists_col (z (M.alpha x))), mul_zero]
  have hdisj : Disjoint c.toFinset (c.toFinset.image M.alpha) := by
    rw [Finset.disjoint_left]
    intro a ha hat
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hat
    exact ((hc b).mp (List.mem_toFinset.mp hb)).2 ((hc _).mp (List.mem_toFinset.mp ha)).1
  have hcover : ∑ x ∈ c.toFinset ∪ c.toFinset.image M.alpha,
      extremalArcEndExists_term M z δ x = ∑ x, extremalArcEndExists_term M z δ x := by
    refine Finset.sum_subset (Finset.subset_univ _) ?_
    intro x _ hx
    exact hoff x (fun h => hx (Finset.mem_union_left _ (List.mem_toFinset.mpr h)))
      (fun h => hx (Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨M.alpha x, List.mem_toFinset.mpr h, M.alpha_involutive x⟩)))
  have himage : ∑ x ∈ c.toFinset.image M.alpha, extremalArcEndExists_term M z δ x =
      ∑ x ∈ c.toFinset, extremalArcEndExists_term M z δ (M.alpha x) :=
    Finset.sum_image fun a _ b _ h => M.alpha.injective h
  rw [← List.sum_toFinset _ hnd, ← hsum, ← hcover, Finset.sum_union hdisj, himage,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun x _ => (extremalArcEndExists_term_add_alpha M z δ x).symm

/-- **Telescoping along a walk segment** `d, B, e`. -/
theorem extremalArcEndExists_telescope (M : CombMap.{v}) (w : M.Vertex) (e : M.Dart)
    (B : List M.Dart) : ∀ d : M.Dart,
      (d :: (B ++ [e])).IsChain (fun a b => M.vertexOf (M.alpha a) = M.vertexOf b) →
        (B.map fun x => extremalArcEndExists_at M w x +
            extremalArcEndExists_at M w (M.alpha x)).sum =
          extremalArcEndExists_at M w (M.alpha d) + extremalArcEndExists_at M w e := by
  induction B with
  | nil =>
    intro d h
    rw [List.nil_append] at h
    rw [List.map_nil, List.sum_nil,
      extremalArcEndExists_at_congr M w (List.isChain_cons_cons.mp h).1,
      extremalArcEndExists_add_self]
  | cons b B ih =>
    intro d h
    rw [List.cons_append] at h
    obtain ⟨h1, h2⟩ := List.isChain_cons_cons.mp h
    simp only [List.map_cons, List.sum_cons]
    rw [ih b h2, extremalArcEndExists_at_congr M w h1]
    exact extremalArcEndExists_add_cancel _ _ _

/-- **A lone removed run is closed**: if every dart of the boundary cycle outside the gap `B`
between the kept darts `d` and `e` is kept and every dart of `B` is removed, then `α d` and `e`
share a vertex.  Parity count at the vertex of `e`. -/
theorem extremalArcEndExists_closed_run (M : CombMap.{v}) {faces : Finset M.Face}
    {c : List M.Dart} (hc : ∀ d, d ∈ c ↔ Surgery.MapCollapse.IsBoundaryDart M faces d)
    (hnd : c.Nodup) (hchain : c.IsChain fun a b => M.vertexOf (M.alpha a) = M.vertexOf b)
    (z : M.Dart → Bool) (hz : ∀ x y, CombMap.FaceClassStep M (walkKeep M c) x y → z x = z y)
    (hind : ∀ d ∈ c, z d = false ∨ z (M.alpha d) = false)
    {A B C : List M.Dart} {d e : M.Dart} (hdec : c = A ++ d :: (B ++ e :: C))
    (hA : ∀ x ∈ A, movePred M z x = true) (hd : movePred M z d = true)
    (hB : ∀ x ∈ B, movePred M z x = false) (he : movePred M z e = true)
    (hC : ∀ x ∈ C, movePred M z x = true) :
    M.vertexOf (M.alpha d) = M.vertexOf e := by
  have hkept : ∀ x, movePred M z x = true →
      extremalArcEndExists_weight M z (extremalArcEndExists_at M (M.vertexOf e)) x = 0 := by
    intro x hx
    obtain ⟨h1, h2⟩ := (movePred_eq_true_iff M z x).mp hx
    unfold extremalArcEndExists_weight
    rw [h1, h2, extremalArcEndExists_add_self (extremalArcEndExists_col false), mul_zero]
  have hremoved : ∀ x ∈ B,
      extremalArcEndExists_weight M z (extremalArcEndExists_at M (M.vertexOf e)) x =
        extremalArcEndExists_at M (M.vertexOf e) x +
          extremalArcEndExists_at M (M.vertexOf e) (M.alpha x) := by
    intro x hx
    have hxc : x ∈ c := by
      rw [hdec]
      simp [hx]
    unfold extremalArcEndExists_weight
    rw [extremalArcEndExists_col_removed (a := z x) (b := z (M.alpha x)) (hB x hx)
      (hind x hxc), mul_one]
  have hsum := extremalArcEndExists_parity M hc hnd z hz
    (extremalArcEndExists_at M (M.vertexOf e)) (extremalArcEndExists_at_sigma M (M.vertexOf e))
  have hch : (d :: (B ++ [e])).IsChain fun a b => M.vertexOf (M.alpha a) = M.vertexOf b :=
    hchain.infix ⟨A, C, by
      rw [hdec]
      simp⟩
  have hT := extremalArcEndExists_telescope M (M.vertexOf e) e B d hch
  rw [hdec, List.map_append, List.sum_append, List.map_cons, List.sum_cons, List.map_append,
    List.sum_append, List.map_cons, List.sum_cons,
    extremalArcEndExists_sum_map_eq_zero
      (extremalArcEndExists_weight M z (extremalArcEndExists_at M (M.vertexOf e))) A
      (fun x hx => hkept x (hA x hx)),
    hkept d hd, hkept e he,
    extremalArcEndExists_sum_map_eq_zero
      (extremalArcEndExists_weight M z (extremalArcEndExists_at M (M.vertexOf e))) C
      (fun x hx => hkept x (hC x hx)),
    extremalArcEndExists_sum_map_congr
      (extremalArcEndExists_weight M z (extremalArcEndExists_at M (M.vertexOf e)))
      (fun x => extremalArcEndExists_at M (M.vertexOf e) x +
        extremalArcEndExists_at M (M.vertexOf e) (M.alpha x)) B hremoved,
    hT, extremalArcEndExists_at_eq_one M (rfl : M.vertexOf e = M.vertexOf e)] at hsum
  simp only [zero_add, add_zero] at hsum
  exact extremalArcEndExists_vertexOf_of_at M (extremalArcEndExists_eq_one_of_add_one _ hsum)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalArcEndExists_col
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalArcEndExists_at
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalArcEndExists_term
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalArcEndExists_weight
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalArcEndExists_add_self
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalArcEndExists_add_cancel
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalArcEndExists_eq_one_of_add_one
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalArcEndExists_col_removed
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalArcEndExists_at_eq_one
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalArcEndExists_at_eq_zero
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalArcEndExists_vertexOf_of_at
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalArcEndExists_at_congr
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalArcEndExists_at_sigma
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalArcEndExists_term_add_alpha
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalArcEndExists_sum_map_eq_zero
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalArcEndExists_sum_map_congr
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalArcEndExists_parity_univ
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalArcEndExists_parity
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalArcEndExists_telescope
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalArcEndExists_closed_run
