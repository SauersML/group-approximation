import GroupApproximation.GGT.VanKampen.NoncrossingClosedWalkSides
import GroupApproximation.Meta.AxiomGuard

/-!
# Two-colouring the faces along a closed walk

Osin, arXiv:math/0411039v3, proof of Lemma 9.7(b):

> "Let us consider the subdiagram `Γ_1` of `Δ` such that: (i) `∂Γ_1 = s_1 t_1 s_2 t_2`, where
> `s_1, s_2` are side arcs of some of `Γ_{i,1}`'s and `t_1, t_2` are subpaths of `∂Π` and the
> section `q_1` of `∂Δ`, respectively; (ii) `Γ_1` contains all `Γ_{i,1}`'s."

The walk `s_1 t_1 s_2 t_2` can pass more than once through a vertex.  `NoncrossingClosedWalkSides`
shows that such a walk bounds a face set when it satisfies a turning condition at every vertex.
This module needs no turning condition.  It two-colours the faces so that the colour changes exactly
across the edges of the walk, and the walk bounds a colour class once all walk darts have their own
faces in that class.

* `ClosedWalkFaceColouring.exists_faceColouring`: in a planar map, a closed walk of distinct edges
  two-colours the faces, the two faces of an edge getting different colours exactly on the edges of
  the walk.  The walk splits at a repeated vertex into two shorter closed walks, and the colourings
  of the pieces add.
* `ClosedWalkFaceColouring.boundaryCycleOfColouring`,
  `ClosedWalkFaceColouring.exists_boundaryCycle_of_orient`: when the faces of all walk darts get one
  colour, the walk is a boundary cycle of that colour class.
* `ClosedWalkFaceColouring.mem_iff_of_eqvGen`: a colour class is constant along faces joined by
  edges off the walk.

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, "Hull's small cancellation theorem", through Osin's
Lemma 4.4); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

open Equiv Surgery.MapCollapse SimpleClosedWalkSides

universe u

namespace ClosedWalkFaceColouring

/-- A list whose consecutive entries are related and whose last entry is related to its first. -/
def ClosedChain {α : Type*} (R : α → α → Prop) (l : List α) : Prop :=
  l.IsChain R ∧ ∀ x ∈ l.getLast?, ∀ y ∈ l.head?, R x y

theorem closedChain_iff {α : Type*} {R : α → α → Prop} {l : List α} (hne : l ≠ []) :
    ClosedChain R l ↔ l.IsChain R ∧ R (l.getLast hne) (l.head hne) := by
  unfold ClosedChain
  rw [List.getLast?_eq_some_getLast hne, List.head?_eq_some_head hne]
  simp

theorem getLast?_append_cons_eq {α : Type*} (l : List α) (a : α) (t : List α) :
    (l ++ a :: t).getLast? = (a :: t).getLast? := by
  simp only [List.getLast?_append, List.getLast?_eq_some_getLast (List.cons_ne_nil a t),
    Option.some_or]

/-- Rotating a closed chain keeps it closed. -/
theorem closedChain_append_comm {α : Type*} {R : α → α → Prop} {P Q : List α}
    (h : ClosedChain R (P ++ Q)) : ClosedChain R (Q ++ P) := by
  rcases P with _ | ⟨p, P⟩
  · simp only [List.nil_append, List.append_nil] at h ⊢
    exact h
  rcases Q with _ | ⟨q, Q⟩
  · simp only [List.nil_append, List.append_nil] at h ⊢
    exact h
  obtain ⟨hc, hclose⟩ := h
  obtain ⟨hP, hQ, hPQ⟩ := List.isChain_append.mp hc
  refine ⟨List.isChain_append.mpr ⟨hQ, hP, fun x hx y hy => hclose x ?_ y hy⟩,
    fun x hx y hy => hPQ x ?_ y hy⟩
  · rw [getLast?_append_cons_eq]
    exact hx
  · rw [getLast?_append_cons_eq] at hx
    exact hx

/-- A closed chain through two entries `d` and `e` that are related to the same entries splits into
the closed chain from `d` to `e` and the closed chain from `e` back to `d`. -/
theorem closedChain_split {α : Type*} {R : α → α → Prop} {d e : α} {X Y : List α}
    (hde : ∀ x, R x d ↔ R x e) (h : ClosedChain R (d :: X ++ e :: Y)) :
    ClosedChain R (d :: X) ∧ ClosedChain R (e :: Y) := by
  obtain ⟨hc, hclose⟩ := h
  obtain ⟨h₁, h₂, h₁₂⟩ := List.isChain_append.mp hc
  refine ⟨⟨h₁, fun x hx y hy => ?_⟩, ⟨h₂, fun x hx y hy => ?_⟩⟩
  · simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
    subst hy
    exact (hde x).mpr (h₁₂ x hx e (Option.mem_def.mpr rfl))
  · simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
    subst hy
    refine (hde x).mp (hclose x ?_ d (Option.mem_def.mpr rfl))
    rw [getLast?_append_cons_eq]
    exact hx

/-- The two faces of an edge get different colours exactly when one of them has the colour and the
other does not. -/
theorem colour_not_iff_iff {a b : Prop} : ¬ (a ↔ b) ↔ (b ∧ ¬ a) ∨ (a ∧ ¬ b) := by
  by_cases ha : a <;> by_cases hb : b <;> simp [ha, hb]

/-- Two colourings add.  If the first colouring separates the faces of an edge exactly when `p`
holds, the second exactly when `q` holds, and `p` and `q` never both hold, then their sum separates
them exactly when `p` or `q` holds. -/
theorem colour_xor_of_exclusive {a₁ a₂ b₁ b₂ p q : Prop} (h₁ : ¬ (a₁ ↔ b₁) ↔ p)
    (h₂ : ¬ (a₂ ↔ b₂) ↔ q) (hexcl : ¬ (p ∧ q)) :
    ¬ (¬ (a₁ ↔ a₂) ↔ ¬ (b₁ ↔ b₂)) ↔ p ∨ q := by
  obtain rfl := propext h₁
  obtain rfl := propext h₂
  by_cases ha₁ : a₁ <;> by_cases ha₂ : a₂ <;> by_cases hb₁ : b₁ <;> by_cases hb₂ : b₂ <;>
    simp_all

theorem exists_faceColouring_aux {M : CombMap.{u}} (hM : M.IsPlanar) (n : ℕ) :
    ∀ w : List M.Dart, w.length = n → w ≠ [] → w.Nodup → (∀ d ∈ w, M.alpha d ∉ w) →
      ClosedChain (fun d e => M.vertexOf (M.alpha d) = M.vertexOf e) w →
      ∃ col : M.Face → Prop,
        ∀ d, ¬ (col (M.faceOf (M.alpha d)) ↔ col (M.faceOf d)) ↔ walkKeep M w d := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro w hlen hne hnodup halpha hcc
    by_cases hv : (w.map M.vertexOf).Nodup
    · have hw : IsNoncrossingClosedWalk M w :=
        IsSimpleClosedWalk.isNoncrossingClosedWalk
          { ne_nil := hne
            chain := ((closedChain_iff hne).mp hcc).1
            closes := ((closedChain_iff hne).mp hcc).2
            vertex_nodup := hv
            alpha_not_mem := halpha }
      refine ⟨fun f => f ∈ sideFaces M w, fun d => ?_⟩
      have h₁ : M.faceOf d ∈ sideFaces M w ∧ M.faceOf (M.alpha d) ∉ sideFaces M w ↔ d ∈ w :=
        hw.isBoundaryDart_sideFaces_iff hM d
      have h₂ := hw.isBoundaryDart_sideFaces_iff hM (M.alpha d)
      change M.faceOf (M.alpha d) ∈ sideFaces M w ∧
        M.faceOf (M.alpha (M.alpha d)) ∉ sideFaces M w ↔ M.alpha d ∈ w at h₂
      rw [M.alpha_involutive d] at h₂
      show ¬ (M.faceOf (M.alpha d) ∈ sideFaces M w ↔ M.faceOf d ∈ sideFaces M w) ↔
        (d ∈ w ∨ M.alpha d ∈ w)
      rw [← h₁, ← h₂]
      exact colour_not_iff_iff
    · obtain ⟨a, ha⟩ : ∃ a, List.Sublist [a, a] (w.map M.vertexOf) := by
        by_contra h
        exact hv (List.nodup_iff_sublist.mpr fun a ha => h ⟨a, ha⟩)
      obtain ⟨l', hl', hmap⟩ := List.sublist_map_iff.mp ha
      rcases l' with _ | ⟨d, _ | ⟨e, _ | ⟨g, t⟩⟩⟩
      · simp at hmap
      · simp at hmap
      · obtain ⟨hda, hea⟩ : a = M.vertexOf d ∧ a = M.vertexOf e := by
          simpa using hmap
        obtain ⟨r₁, r₂, rfl, hd, he⟩ := List.cons_sublist_iff.mp hl'
        obtain ⟨A, B, rfl⟩ := List.append_of_mem hd
        obtain ⟨C, D, rfl⟩ := List.append_of_mem (List.singleton_sublist.mp he)
        have hw₁ : A ++ d :: B ++ (C ++ e :: D) = A ++ (d :: (B ++ C) ++ e :: D) := by simp
        have hw₂ : d :: (B ++ C) ++ e :: D ++ A = d :: (B ++ C) ++ e :: (D ++ A) := by simp
        rw [hw₁] at hcc
        have hrot := closedChain_append_comm hcc
        rw [hw₂] at hrot
        have hvde : ∀ x, M.vertexOf (M.alpha x) = M.vertexOf d ↔
            M.vertexOf (M.alpha x) = M.vertexOf e := fun x => by
          rw [← hda, ← hea]
        obtain ⟨hc₁, hc₂⟩ :=
          closedChain_split (R := fun x y => M.vertexOf (M.alpha x) = M.vertexOf y) hvde hrot
        have hperm : List.Perm (d :: (B ++ C) ++ e :: (D ++ A)) (A ++ d :: B ++ (C ++ e :: D)) := by
          rw [← hw₂, hw₁]
          exact List.perm_append_comm
        obtain ⟨hnd₁, hnd₂, hdisj⟩ := List.nodup_append.mp (hperm.nodup_iff.mpr hnodup)
        have hmem : ∀ x, x ∈ A ++ d :: B ++ (C ++ e :: D) ↔
            x ∈ d :: (B ++ C) ∨ x ∈ e :: (D ++ A) := fun x => by
          rw [← hperm.mem_iff, List.mem_append]
        have halpha₁ : ∀ x ∈ d :: (B ++ C), M.alpha x ∉ d :: (B ++ C) := fun x hx hax =>
          halpha x ((hmem x).mpr (Or.inl hx)) ((hmem (M.alpha x)).mpr (Or.inl hax))
        have halpha₂ : ∀ x ∈ e :: (D ++ A), M.alpha x ∉ e :: (D ++ A) := fun x hx hax =>
          halpha x ((hmem x).mpr (Or.inr hx)) ((hmem (M.alpha x)).mpr (Or.inr hax))
        have hlen₁ : (d :: (B ++ C)).length < n := by
          simp only [List.length_append, List.length_cons] at hlen ⊢
          omega
        have hlen₂ : (e :: (D ++ A)).length < n := by
          simp only [List.length_append, List.length_cons] at hlen ⊢
          omega
        obtain ⟨col₁, hcol₁⟩ :=
          ih _ hlen₁ (d :: (B ++ C)) rfl (List.cons_ne_nil _ _) hnd₁ halpha₁ hc₁
        obtain ⟨col₂, hcol₂⟩ :=
          ih _ hlen₂ (e :: (D ++ A)) rfl (List.cons_ne_nil _ _) hnd₂ halpha₂ hc₂
        refine ⟨fun f => ¬ (col₁ f ↔ col₂ f), fun x => ?_⟩
        have hkeep : walkKeep M (A ++ d :: B ++ (C ++ e :: D)) x ↔
            walkKeep M (d :: (B ++ C)) x ∨ walkKeep M (e :: (D ++ A)) x := by
          unfold walkKeep
          rw [hmem x, hmem (M.alpha x)]
          exact or_or_or_comm
        have hexcl : ¬ (walkKeep M (d :: (B ++ C)) x ∧ walkKeep M (e :: (D ++ A)) x) := by
          unfold walkKeep
          rintro ⟨hx₁ | hx₁, hx₂ | hx₂⟩
          · exact hdisj x hx₁ x hx₂ rfl
          · exact halpha x ((hmem x).mpr (Or.inl hx₁)) ((hmem (M.alpha x)).mpr (Or.inr hx₂))
          · exact halpha x ((hmem x).mpr (Or.inr hx₂)) ((hmem (M.alpha x)).mpr (Or.inl hx₁))
          · exact hdisj _ hx₁ _ hx₂ rfl
        exact (colour_xor_of_exclusive (hcol₁ x) (hcol₂ x) hexcl).trans hkeep.symm
      · simp at hmap

/-- **Two-colouring the faces along a closed walk.**  In a planar map, let `w` be a closed walk
using no edge twice.  The faces can be coloured in two colours so that the two faces of an edge get
different colours exactly when the edge is an edge of `w`.  If no two darts of `w` start at the
same vertex, the faces on the side of the walk are one colour.  Otherwise the walk splits at a
repeated vertex into two shorter closed walks with disjoint edges, and the colourings add. -/
theorem exists_faceColouring {M : CombMap.{u}} (hM : M.IsPlanar) {w : List M.Dart}
    (hne : w ≠ []) (hnodup : w.Nodup) (halpha : ∀ d ∈ w, M.alpha d ∉ w)
    (hchain : w.IsChain fun d e => M.vertexOf (M.alpha d) = M.vertexOf e)
    (hcloses : M.vertexOf (M.alpha (w.getLast hne)) = M.vertexOf (w.head hne)) :
    ∃ col : M.Face → Prop,
      ∀ d, ¬ (col (M.faceOf (M.alpha d)) ↔ col (M.faceOf d)) ↔ walkKeep M w d :=
  exists_faceColouring_aux hM w.length w rfl hne hnodup halpha
    ((closedChain_iff hne).mpr ⟨hchain, hcloses⟩)

/-- The two-colouring of `exists_faceColouring`, as the face set of one colour. -/
theorem exists_faceSet_colouring {M : CombMap.{u}} (hM : M.IsPlanar) {w : List M.Dart}
    (hne : w ≠ []) (hnodup : w.Nodup) (halpha : ∀ d ∈ w, M.alpha d ∉ w)
    (hchain : w.IsChain fun d e => M.vertexOf (M.alpha d) = M.vertexOf e)
    (hcloses : M.vertexOf (M.alpha (w.getLast hne)) = M.vertexOf (w.head hne)) :
    ∃ faces : Finset M.Face,
      ∀ d, ¬ (M.faceOf (M.alpha d) ∈ faces ↔ M.faceOf d ∈ faces) ↔ walkKeep M w d := by
  classical
  obtain ⟨col, hcol⟩ := exists_faceColouring hM hne hnodup halpha hchain hcloses
  refine ⟨Finset.univ.filter col, fun d => ?_⟩
  rw [← hcol d]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- The other colour class changes colour across the same edges. -/
theorem colouring_compl {M : CombMap.{u}} [DecidableEq M.Face] {w : List M.Dart}
    {faces : Finset M.Face}
    (hcol : ∀ d, ¬ (M.faceOf (M.alpha d) ∈ faces ↔ M.faceOf d ∈ faces) ↔ walkKeep M w d) :
    ∀ d, ¬ (M.faceOf (M.alpha d) ∈ facesᶜ ↔ M.faceOf d ∈ facesᶜ) ↔ walkKeep M w d := by
  intro d
  rw [← hcol d, Finset.mem_compl, Finset.mem_compl]
  tauto

/-- A colour class does not change across an edge off the walk. -/
theorem mem_iff_mem_alpha_of_not_walkKeep {M : CombMap.{u}} {w : List M.Dart}
    {faces : Finset M.Face}
    (hcol : ∀ d, ¬ (M.faceOf (M.alpha d) ∈ faces ↔ M.faceOf d ∈ faces) ↔ walkKeep M w d)
    {d : M.Dart} (hd : ¬ walkKeep M w d) :
    M.faceOf (M.alpha d) ∈ faces ↔ M.faceOf d ∈ faces :=
  not_not.mp fun h => hd ((hcol d).mp h)

/-- **A colour class is constant along faces joined by edges off the walk.**  Let every step of
the relation `r` cross an edge off the walk.  Then faces in one class of the equivalence generated
by `r` are all in the colour class or all outside it. -/
theorem mem_iff_of_eqvGen {M : CombMap.{u}} {w : List M.Dart} {faces : Finset M.Face}
    (hcol : ∀ d, ¬ (M.faceOf (M.alpha d) ∈ faces ↔ M.faceOf d ∈ faces) ↔ walkKeep M w d)
    {r : M.Face → M.Face → Prop}
    (hr : ∀ f g, r f g → ∃ d, M.faceOf d = f ∧ M.faceOf (M.alpha d) = g ∧ ¬ walkKeep M w d)
    {f g : M.Face} (h : Relation.EqvGen r f g) : f ∈ faces ↔ g ∈ faces := by
  induction h with
  | rel f g hfg =>
    obtain ⟨d, rfl, rfl, hd⟩ := hr f g hfg
    exact (mem_iff_mem_alpha_of_not_walkKeep hcol hd).symm
  | refl => exact Iff.rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- **A closed walk bounds a colour class.**  Let the faces in `faces` and the other faces meet
exactly across the edges of the walk `w`, and let every walk dart have its own face in `faces`.
Then `w` is a boundary cycle of `faces`. -/
def boundaryCycleOfColouring {M : CombMap.{u}} {w : List M.Dart} {faces : Finset M.Face}
    (hne : w ≠ []) (hnodup : w.Nodup)
    (hcol : ∀ d, ¬ (M.faceOf (M.alpha d) ∈ faces ↔ M.faceOf d ∈ faces) ↔ walkKeep M w d)
    (horient : ∀ d ∈ w, M.faceOf d ∈ faces) : BoundaryCycle M faces where
  cycle := w
  cycle_nonempty := hne
  cycle_nodup := hnodup
  cycle_mem_iff d := by
    show d ∈ w ↔ M.faceOf d ∈ faces ∧ M.faceOf (M.alpha d) ∉ faces
    constructor
    · intro hd
      have hf := horient d hd
      exact ⟨hf, fun hfa => (hcol d).mpr (Or.inl hd) ⟨fun _ => hf, fun _ => hfa⟩⟩
    · rintro ⟨hf, hfa⟩
      rcases (hcol d).mp fun h => hfa (h.mpr hf) with hd | hd
      · exact hd
      · exact (hfa (horient _ hd)).elim

/-- **A closed walk whose darts turn one way bounds a face set.**  In a planar map, let `w` be a
closed walk using no edge twice.  Suppose that whenever a face set and its complement meet exactly
across the edges of `w`, the faces of all walk darts lie on one side.  Then `w` is a boundary cycle
of a face set. -/
theorem exists_boundaryCycle_of_orient {M : CombMap.{u}} (hM : M.IsPlanar) {w : List M.Dart}
    (hne : w ≠ []) (hnodup : w.Nodup) (halpha : ∀ d ∈ w, M.alpha d ∉ w)
    (hchain : w.IsChain fun d e => M.vertexOf (M.alpha d) = M.vertexOf e)
    (hcloses : M.vertexOf (M.alpha (w.getLast hne)) = M.vertexOf (w.head hne))
    (horient : ∀ faces : Finset M.Face,
      (∀ d, ¬ (M.faceOf (M.alpha d) ∈ faces ↔ M.faceOf d ∈ faces) ↔ walkKeep M w d) →
        ∀ d ∈ w, ∀ e ∈ w, (M.faceOf d ∈ faces ↔ M.faceOf e ∈ faces)) :
    ∃ (faces : Finset M.Face) (B : BoundaryCycle M faces), B.cycle = w := by
  classical
  obtain ⟨faces, hcol⟩ := exists_faceSet_colouring hM hne hnodup halpha hchain hcloses
  have h₀ := List.head_mem hne
  by_cases hin : M.faceOf (w.head hne) ∈ faces
  · exact ⟨faces, boundaryCycleOfColouring hne hnodup hcol
      fun d hd => (horient faces hcol d hd _ h₀).mpr hin, rfl⟩
  · exact ⟨facesᶜ, boundaryCycleOfColouring hne hnodup (colouring_compl hcol)
      fun d hd => Finset.mem_compl.mpr fun hd' => hin ((horient faces hcol d hd _ h₀).mp hd'),
      rfl⟩

end ClosedWalkFaceColouring

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.ClosedWalkFaceColouring.colour_not_iff_iff
#audit_axioms GroupApproximation.GGT.VanKampen.ClosedWalkFaceColouring.colour_xor_of_exclusive
#audit_axioms GroupApproximation.GGT.VanKampen.ClosedWalkFaceColouring.exists_faceColouring
#audit_axioms GroupApproximation.GGT.VanKampen.ClosedWalkFaceColouring.exists_faceSet_colouring
#audit_axioms GroupApproximation.GGT.VanKampen.ClosedWalkFaceColouring.colouring_compl
#audit_axioms GroupApproximation.GGT.VanKampen.ClosedWalkFaceColouring.mem_iff_mem_alpha_of_not_walkKeep
#audit_axioms GroupApproximation.GGT.VanKampen.ClosedWalkFaceColouring.mem_iff_of_eqvGen
#audit_axioms GroupApproximation.GGT.VanKampen.ClosedWalkFaceColouring.boundaryCycleOfColouring
#audit_axioms GroupApproximation.GGT.VanKampen.ClosedWalkFaceColouring.exists_boundaryCycle_of_orient
