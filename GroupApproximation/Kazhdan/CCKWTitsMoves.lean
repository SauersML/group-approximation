import GroupApproximation.GGT.SystolicDefs
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Data.List.Destutter
import Mathlib.Data.List.Chain
import GroupApproximation.Meta.AxiomGuard

/-!
# The coset complex of three subgroups, and relaxed homotopy moves

For a group `G` and subgroups `H : Fin 3 → Subgroup G`, the coset complex `titsComplex G H`
has the cosets `g Hᵢ` of all three types as vertices.  A vertex `v` is *represented* by `g`
when it is the coset of `g` (`Rep`).  Two vertices of different types are adjacent when they
have a common representative, and three vertices of pairwise different types span a triangle
when they have a common representative.

Simple connectivity asks that every closed edge path reduce to a point under backtracking and
triangle moves.  This module relaxes the moves (`Moves`): a middle vertex among three with a
common representative may be removed, and a repeated vertex may be removed.  Removing
consecutive duplicates (`List.destutter`) turns every relaxed move into a genuine
backtracking or triangle move or into an equality (`moves_destutter`), and closed edge paths
contain no duplicates, so the relaxed moves suffice (`simplyConnected_of_moves`).
-/

namespace GroupApproximation.CCKWTits

open Systolic

universe u

variable {G : Type u} [Group G] (H : Fin 3 → Subgroup G)

/-- `g` represents the vertex `v`: `v` is the coset of `g` of its type. -/
def Rep (v : Σ i : Fin 3, G ⧸ H i) (g : G) : Prop :=
  v.2 = (QuotientGroup.mk g : G ⧸ H v.1)

/-- The vertex of type `i` at `g`. -/
def vtx (i : Fin 3) (g : G) : Σ i : Fin 3, G ⧸ H i :=
  ⟨i, (QuotientGroup.mk g : G ⧸ H i)⟩

/-- **The coset complex of three subgroups**: distinct types with a common representative are
adjacent; pairwise distinct types with a common representative span a triangle. -/
def titsComplex (G : Type u) [Group G] (H : Fin 3 → Subgroup G) :
    TriangleComplex (Σ i : Fin 3, G ⧸ H i) where
  G :=
    { Adj := fun v w ↦ v.1 ≠ w.1 ∧ ∃ g, Rep H v g ∧ Rep H w g
      symm := ⟨fun _ _ ⟨hne, g, hv, hw⟩ ↦ ⟨hne.symm, g, hw, hv⟩⟩
      loopless := ⟨fun _ ⟨hne, _⟩ ↦ hne rfl⟩ }
  Tri := fun u v w ↦ u.1 ≠ v.1 ∧ v.1 ≠ w.1 ∧ u.1 ≠ w.1 ∧ ∃ g, Rep H u g ∧ Rep H v g ∧ Rep H w g
  tri_swap12 := by
    rintro x y z ⟨h12, h23, h13, g, hx, hy, hz⟩
    exact ⟨h12.symm, h13, h23, g, hy, hx, hz⟩
  tri_swap23 := by
    rintro x y z ⟨h12, h23, h13, g, hx, hy, hz⟩
    exact ⟨h13, h23.symm, h12, g, hx, hz, hy⟩
  tri_adj := by
    rintro x y z ⟨h12, h23, h13, g, hx, hy, hz⟩
    exact ⟨⟨h12, g, hx, hy⟩, ⟨h23, g, hy, hz⟩, ⟨h13, g, hx, hz⟩⟩

/-! ### Representatives -/

variable {H}

theorem rep_vtx (i : Fin 3) (g : G) : Rep H (vtx H i g) g := rfl

theorem exists_rep (v : Σ i : Fin 3, G ⧸ H i) : ∃ g, Rep H v g := by
  obtain ⟨i, x⟩ := v
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective x
  exact ⟨g, hg.symm⟩

theorem vtx_eq_of_rep {v : Σ i : Fin 3, G ⧸ H i} {g : G} (hv : Rep H v g) : vtx H v.1 g = v := by
  obtain ⟨i, x⟩ := v
  dsimp only [Rep] at hv
  unfold vtx
  rw [hv]

theorem eq_of_rep {v w : Σ i : Fin 3, G ⧸ H i} {g : G} (hv : Rep H v g) (hw : Rep H w g)
    (h : v.1 = w.1) : v = w := by
  rw [← vtx_eq_of_rep hv, ← vtx_eq_of_rep hw, h]

theorem type_ne_of_rep {v w : Σ i : Fin 3, G ⧸ H i} {g : G} (hv : Rep H v g) (hw : Rep H w g)
    (hne : v ≠ w) : v.1 ≠ w.1 :=
  fun h ↦ hne (eq_of_rep hv hw h)

theorem rep_mul {v : Σ i : Fin 3, G ⧸ H i} {g p : G} (hv : Rep H v g) (hp : p ∈ H v.1) :
    Rep H v (g * p) := by
  unfold Rep at hv ⊢
  rw [hv]
  exact QuotientGroup.eq.mpr (by rwa [inv_mul_cancel_left])

theorem mem_of_rep_rep {v : Σ i : Fin 3, G ⧸ H i} {g k : G} (hg : Rep H v g) (hk : Rep H v k) :
    g⁻¹ * k ∈ H v.1 :=
  QuotientGroup.eq.mp (hg.symm.trans hk)

theorem adj_of_rep_ne {v w : Σ i : Fin 3, G ⧸ H i} {g : G} (hv : Rep H v g) (hw : Rep H w g)
    (hne : v ≠ w) : (titsComplex G H).G.Adj v w :=
  ⟨type_ne_of_rep hv hw hne, g, hv, hw⟩

/-! ### Relaxed moves -/

variable (H)

/-- **Relaxed homotopy moves**: remove the middle one of three consecutive vertices with a
common representative, or remove a repeated vertex. -/
inductive Moves : List (Σ i : Fin 3, G ⧸ H i) → List (Σ i : Fin 3, G ⧸ H i) → Prop
  | cp (p q : List (Σ i : Fin 3, G ⧸ H i)) (u v w : Σ i : Fin 3, G ⧸ H i) (g : G)
      (hu : Rep H u g) (hv : Rep H v g) (hw : Rep H w g) :
      Moves (p ++ u :: v :: w :: q) (p ++ u :: w :: q)
  | stutter (p q : List (Σ i : Fin 3, G ⧸ H i)) (u : Σ i : Fin 3, G ⧸ H i) :
      Moves (p ++ u :: u :: q) (p ++ u :: q)

variable {H}

/-- Transport of an equivalence closure along a map. -/
theorem eqvGen_map {α β : Type*} {r : α → α → Prop} {s : β → β → Prop} (f : α → β)
    (hf : ∀ a b, r a b → Relation.EqvGen s (f a) (f b)) {a b : α} (h : Relation.EqvGen r a b) :
    Relation.EqvGen s (f a) (f b) := by
  induction h with
  | rel x y hxy => exact hf x y hxy
  | refl x => exact Relation.EqvGen.refl _
  | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans x y z _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

theorem eqvGen_of_eq {α : Type*} {r : α → α → Prop} {a b : α} (h : a = b) :
    Relation.EqvGen r a b :=
  h ▸ Relation.EqvGen.refl a

theorem moves_append_left (r : List (Σ i : Fin 3, G ⧸ H i)) {l l' : List (Σ i : Fin 3, G ⧸ H i)}
    (h : Moves H l l') : Moves H (r ++ l) (r ++ l') := by
  cases h with
  | cp p q u v w g hu hv hw =>
      simpa only [List.append_assoc] using Moves.cp (r ++ p) q u v w g hu hv hw
  | stutter p q u => simpa only [List.append_assoc] using Moves.stutter (H := H) (r ++ p) q u

theorem moves_append_right (r : List (Σ i : Fin 3, G ⧸ H i)) {l l' : List (Σ i : Fin 3, G ⧸ H i)}
    (h : Moves H l l') : Moves H (l ++ r) (l' ++ r) := by
  cases h with
  | cp p q u v w g hu hv hw =>
      simpa only [List.append_assoc, List.cons_append] using Moves.cp p (q ++ r) u v w g hu hv hw
  | stutter p q u =>
      simpa only [List.append_assoc, List.cons_append] using Moves.stutter (H := H) p (q ++ r) u

theorem eqvGen_moves_append_left (r : List (Σ i : Fin 3, G ⧸ H i))
    {l l' : List (Σ i : Fin 3, G ⧸ H i)} (h : Relation.EqvGen (Moves H) l l') :
    Relation.EqvGen (Moves H) (r ++ l) (r ++ l') :=
  eqvGen_map (fun x ↦ r ++ x) (fun _ _ hab ↦ Relation.EqvGen.rel _ _ (moves_append_left r hab)) h

theorem eqvGen_moves_append_right (r : List (Σ i : Fin 3, G ⧸ H i))
    {l l' : List (Σ i : Fin 3, G ⧸ H i)} (h : Relation.EqvGen (Moves H) l l') :
    Relation.EqvGen (Moves H) (l ++ r) (l' ++ r) :=
  eqvGen_map (fun x ↦ x ++ r) (fun _ _ hab ↦ Relation.EqvGen.rel _ _ (moves_append_right r hab)) h

/-! ### Removing consecutive duplicates -/

section Destutter

variable {α : Type*} [DecidableEq α]

theorem destutter'_self_cons (a : α) (l : List α) :
    (a :: l).destutter' (· ≠ ·) a = l.destutter' (· ≠ ·) a := by
  rw [List.destutter'_cons, if_neg (not_not.mpr rfl)]

theorem destutter'_ne_cons {a b : α} (h : a ≠ b) (l : List α) :
    (b :: l).destutter' (· ≠ ·) a = a :: l.destutter' (· ≠ ·) b := by
  rw [List.destutter'_cons, if_pos h]

theorem exists_destutter'_eq_cons (a : α) (l : List α) : ∃ Q, l.destutter' (· ≠ ·) a = a :: Q := by
  induction l generalizing a with
  | nil => exact ⟨[], rfl⟩
  | cons b l ih =>
      by_cases h : a ≠ b
      · exact ⟨_, destutter'_ne_cons h l⟩
      · rw [List.destutter'_cons, if_neg h]
        exact ih a

theorem exists_destutter'_append (u : α) :
    ∀ (p : List α) (a : α), ∃ P : List α, ∀ q : List α,
      (p ++ u :: q).destutter' (· ≠ ·) a = P ++ q.destutter' (· ≠ ·) u
  | [], a => by
      by_cases h : a ≠ u
      · exact ⟨[a], fun q ↦ by
          rw [List.nil_append, destutter'_ne_cons h, List.singleton_append]⟩
      · have hau : a = u := not_not.mp h
        subst hau
        exact ⟨[], fun q ↦ by rw [List.nil_append, destutter'_self_cons, List.nil_append]⟩
  | b :: p, a => by
      by_cases h : a ≠ b
      · obtain ⟨P, hP⟩ := exists_destutter'_append u p b
        exact ⟨a :: P, fun q ↦ by rw [List.cons_append, destutter'_ne_cons h, hP, List.cons_append]⟩
      · have hab : a = b := not_not.mp h
        subst hab
        obtain ⟨P, hP⟩ := exists_destutter'_append u p a
        exact ⟨P, fun q ↦ by rw [List.cons_append, destutter'_self_cons, hP]⟩

theorem exists_destutter_append (p : List α) (u : α) :
    ∃ P : List α, ∀ q : List α, (p ++ u :: q).destutter (· ≠ ·) = P ++ q.destutter' (· ≠ ·) u := by
  cases p with
  | nil => exact ⟨[], fun q ↦ by rw [List.nil_append, List.destutter_cons', List.nil_append]⟩
  | cons a p =>
      obtain ⟨P, hP⟩ := exists_destutter'_append u p a
      exact ⟨P, fun q ↦ by rw [List.cons_append, List.destutter_cons', hP]⟩

end Destutter

/-- **A relaxed move becomes a genuine move after removing duplicates.** -/
theorem moves_destutter [DecidableEq (Σ i : Fin 3, G ⧸ H i)] {l l' : List (Σ i : Fin 3, G ⧸ H i)}
    (h : Moves H l l') :
    Relation.EqvGen (TriangleMove (titsComplex G H)) (l.destutter (· ≠ ·)) (l'.destutter (· ≠ ·)) := by
  cases h with
  | cp p q u v w g hu hv hw =>
      obtain ⟨P, hP⟩ := exists_destutter_append p u
      rw [hP, hP]
      by_cases huv : u = v
      · subst huv
        exact eqvGen_of_eq (by rw [destutter'_self_cons])
      by_cases hvw : v = w
      · subst hvw
        exact eqvGen_of_eq (by
          rw [destutter'_ne_cons huv, destutter'_ne_cons huv, destutter'_self_cons])
      by_cases huw : u = w
      · subst huw
        obtain ⟨Q, hQ⟩ := exists_destutter'_eq_cons u q
        rw [destutter'_ne_cons huv, destutter'_ne_cons hvw, destutter'_self_cons, hQ]
        exact Relation.EqvGen.rel _ _ (TriangleMove.backtrack P Q u v (adj_of_rep_ne hu hv huv))
      · obtain ⟨Q, hQ⟩ := exists_destutter'_eq_cons w q
        rw [destutter'_ne_cons huv, destutter'_ne_cons hvw, destutter'_ne_cons huw, hQ]
        exact Relation.EqvGen.rel _ _ (TriangleMove.triangle P Q u v w
          ⟨type_ne_of_rep hu hv huv, type_ne_of_rep hv hw hvw, type_ne_of_rep hu hw huw,
            g, hu, hv, hw⟩)
  | stutter p q u =>
      obtain ⟨P, hP⟩ := exists_destutter_append p u
      exact eqvGen_of_eq (by rw [hP, hP, destutter'_self_cons])

theorem eqvGen_destutter [DecidableEq (Σ i : Fin 3, G ⧸ H i)] {l l' : List (Σ i : Fin 3, G ⧸ H i)}
    (h : Relation.EqvGen (Moves H) l l') :
    Relation.EqvGen (TriangleMove (titsComplex G H)) (l.destutter (· ≠ ·)) (l'.destutter (· ≠ ·)) :=
  eqvGen_map (fun x ↦ x.destutter (· ≠ ·)) (fun _ _ hab ↦ moves_destutter hab) h

/-- **Relaxed moves suffice for simple connectivity.** -/
theorem simplyConnected_of_moves
    (h : ∀ (v : Σ i : Fin 3, G ⧸ H i) (l : List (Σ i : Fin 3, G ⧸ H i)),
      List.IsChain (titsComplex G H).G.Adj (v :: l ++ [v]) →
        Relation.EqvGen (Moves H) (v :: l ++ [v]) [v]) :
    SimplyConnected (titsComplex G H) := by
  classical
  intro v l hchain
  have hd := eqvGen_destutter (h v l hchain)
  have hc : List.IsChain (· ≠ ·) (v :: l ++ [v]) := hchain.imp fun _ _ hab ↦ hab.ne
  rwa [List.destutter_of_isChain (R := (· ≠ ·)) _ hc,
    List.destutter_of_isChain (R := (· ≠ ·)) _ (List.isChain_singleton v)] at hd

end GroupApproximation.CCKWTits

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.CCKWTits.eq_of_rep
#audit_axioms GroupApproximation.CCKWTits.rep_mul
#audit_axioms GroupApproximation.CCKWTits.moves_append_right
#audit_axioms GroupApproximation.CCKWTits.exists_destutter_append
#audit_axioms GroupApproximation.CCKWTits.moves_destutter
#audit_axioms GroupApproximation.CCKWTits.simplyConnected_of_moves
