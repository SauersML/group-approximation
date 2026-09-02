import GroupApproximation.GGT.VanKampen.FaceSetBoundaryWalk

/-!
# A boundary run extends to a rotation of its face boundary

A planar ear has to supply two lists: the arc of the boundary cycle carried by
the peeled face, and the rest of that face's boundary.  This file shows the
second one is free.  If a nonempty duplicate-free list of darts all lies on one
face and is chained by the face rotation, then it is an initial segment of some
rotation of the stored `Delta.faceBoundary` of that face.

So a producer of the planar ear only has to exhibit the arc: that it is a
contiguous block of the boundary cycle, that its darts lie on the chosen face,
and that consecutive darts follow the face rotation, which is exactly what
`boundaryStep_eq_facePerm` gives along a run of the boundary walk.  The
`faceRotation` and `face_eq` fields of `FaceSetEar` follow from this theorem.

The generic list lemmas at the top are the cyclic-rotation bookkeeping: a chain
whose last element relates back to its first stays a chain after any rotation,
and two lists agreeing at every common index with the first no longer than the
second are prefix and whole.
-/

namespace GroupApproximation
namespace GGT
namespace VanKampen
namespace Embedded

open GroupApproximation.HullSC

universe u w v

/-! ## Generic cyclic-list bookkeeping -/

private theorem getLast_drop_eq_getLast
    {α : Type*} {cycle : List α} (hne : cycle ≠ [])
    {k : ℕ} (hdrop : cycle.drop k ≠ []) :
    (cycle.drop k).getLast hdrop = cycle.getLast hne := by
  have hsplit : cycle.take k ++ cycle.drop k = cycle :=
    List.take_append_drop k cycle
  have hsplit_ne : cycle.take k ++ cycle.drop k ≠ [] := by
    rw [hsplit]
    exact hne
  calc
    (cycle.drop k).getLast hdrop =
        (cycle.take k ++ cycle.drop k).getLast hsplit_ne := by
      symm
      exact List.getLast_append_of_right_ne_nil _ _ hdrop
    _ = cycle.getLast hne := List.getLast_congr hsplit_ne hne hsplit

private theorem head_take_eq_head
    {α : Type*} {cycle : List α} (hne : cycle ≠ [])
    {k : ℕ} (htake : cycle.take k ≠ []) :
    (cycle.take k).head htake = cycle.head hne := by
  cases cycle with
  | nil => exact (hne rfl).elim
  | cons a tail =>
      cases k with
      | zero => exact (htake rfl).elim
      | succ k => rfl

private theorem head_eq_of_mem_head?
    {α : Type*} {cycle : List α} (hne : cycle ≠ [])
    {d : α} (hd : d ∈ cycle.head?) : d = cycle.head hne := by
  cases cycle with
  | nil => exact (hne rfl).elim
  | cons a tail =>
      have hmem : a = d := by
        simpa only [List.head?, Option.mem_def, Option.some_inj] using hd
      exact hmem.symm

/-- A chain whose last element relates back to its first stays a chain after
any cyclic rotation. -/
theorem isChain_rotate_of_closes
    {α : Type*} {R : α → α → Prop} {cycle : List α}
    (hne : cycle ≠ []) (hchain : cycle.IsChain R)
    (hclose : R (cycle.getLast hne) (cycle.head hne)) (n : ℕ) :
    (cycle.rotate n).IsChain R := by
  have hlen : 0 < cycle.length := List.length_pos_of_ne_nil hne
  let k : ℕ := n % cycle.length
  have hrot : cycle.rotate n = cycle.drop k ++ cycle.take k := by
    dsimp [k]
    exact List.rotate_eq_drop_append_take_mod
  by_cases hkzero : k = 0
  · rw [hrot, hkzero]
    simpa using hchain
  have hktake : cycle.take k ≠ [] := by
    intro hnil
    rw [List.take_eq_nil_iff] at hnil
    rcases hnil with hkzero' | hcycle
    · exact hkzero hkzero'
    · exact (hne hcycle).elim
  have hklt : k < cycle.length := Nat.mod_lt n hlen
  have hkdrop : cycle.drop k ≠ [] := by
    intro hnil
    rw [List.drop_eq_nil_iff] at hnil
    omega
  have hrot_chain : (cycle.drop k ++ cycle.take k).IsChain R := by
    apply List.IsChain.append (hchain.drop k) (hchain.take k)
    intro x hx y hy
    have hxlast : x = (cycle.drop k).getLast hkdrop := by
      obtain ⟨_, hxEq⟩ := List.mem_getLast?_eq_getLast hx
      exact hxEq
    have hyhead : y = (cycle.take k).head hktake :=
      head_eq_of_mem_head? hktake hy
    rw [hxlast, hyhead, getLast_drop_eq_getLast hne hkdrop,
      head_take_eq_head hne hktake]
    exact hclose
  rw [hrot]
  exact hrot_chain

/-- Rotating to the position of a distinguished element puts it at the head. -/
private theorem rotate_append_cons
    {α : Type*} (pre : List α) (a : α) (suf : List α) :
    (pre ++ a :: suf).rotate pre.length = a :: (suf ++ pre) := by
  rw [List.rotate_append_length_eq, List.cons_append]

/-- A list which agrees with a no shorter list at every common index is an
initial segment of it. -/
private theorem exists_append_of_getElem_eq
    {α : Type*} : ∀ (first second : List α), first.length ≤ second.length →
      (∀ (i : ℕ) (h₁ : i < first.length) (h₂ : i < second.length),
        first[i] = second[i]) →
      ∃ rest : List α, second = first ++ rest
  | [], second, _, _ => ⟨second, rfl⟩
  | _ :: _, [], hlen, _ => by
      exfalso
      simp only [List.length_cons, List.length_nil] at hlen
      omega
  | a :: t₁, b :: t₂, hlen, h => by
      have hab : a = b := by
        have h0 := h 0 (by simp) (by simp)
        simpa using h0
      have hlen' : t₁.length ≤ t₂.length := by
        simp only [List.length_cons] at hlen
        omega
      have h' : ∀ (i : ℕ) (h₁ : i < t₁.length) (h₂ : i < t₂.length),
          t₁[i] = t₂[i] := by
        intro i h₁ h₂
        have hi := h (i + 1) (by simpa using h₁) (by simpa using h₂)
        simpa using hi
      obtain ⟨rest, hrest⟩ := exists_append_of_getElem_eq t₁ t₂ hlen' h'
      exact ⟨rest, by rw [hab, hrest]⟩

variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (GGT.RelLetter G Lambda))}
  {Delta : DiscDiagram.{u, w, v} W}

/-! ## A run along one face -/

/-- A nonempty duplicate-free list of darts of one face, chained by the face
rotation, is an initial segment of a rotation of that face's stored boundary.
The remaining segment is the `interior` of a planar ear. -/
theorem exists_faceBoundary_rotate_eq_append
    {face : Delta.toCombMap.Face} {arc : List Delta.toCombMap.Dart}
    (harc : arc ≠ []) (hnodup : arc.Nodup)
    (hface : ∀ d ∈ arc, Delta.toCombMap.faceOf d = face)
    (hchain : arc.IsChain fun d e => Delta.toCombMap.facePerm d = e) :
    ∃ (k : ℕ) (interior : List Delta.toCombMap.Dart),
      (Delta.faceBoundary face).darts.rotate k = arc ++ interior := by
  have hpos : 0 < arc.length := List.length_pos_of_ne_nil harc
  have hsub : arc ⊆ (Delta.faceBoundary face).darts := by
    intro d hd
    exact ((Delta.faceBoundary face).mem_iff d).2 (hface d hd)
  have hlen : arc.length ≤ (Delta.faceBoundary face).darts.length :=
    (List.subperm_of_subset hnodup hsub).length_le
  have hd₀ : arc[0] ∈ (Delta.faceBoundary face).darts :=
    hsub (List.getElem_mem hpos)
  obtain ⟨pre, suf, hsplit⟩ := List.append_of_mem hd₀
  have hrot : (Delta.faceBoundary face).darts.rotate pre.length =
      arc[0] :: (suf ++ pre) := by
    rw [hsplit]
    exact rotate_append_cons pre arc[0] suf
  have hrotchain : (arc[0] :: (suf ++ pre)).IsChain
      (fun d e => Delta.toCombMap.facePerm d = e) := by
    rw [← hrot]
    exact isChain_rotate_of_closes (Delta.faceBoundary face).nonempty
      (Delta.faceBoundary face).chain (Delta.faceBoundary face).closes
      pre.length
  have hlen2 : arc.length ≤ (arc[0] :: (suf ++ pre)).length := by
    rw [← hrot, List.length_rotate]
    exact hlen
  have hgetElem : ∀ (i : ℕ) (h₁ : i < arc.length)
      (h₂ : i < (arc[0] :: (suf ++ pre)).length),
      arc[i] = (arc[0] :: (suf ++ pre))[i] := by
    intro i h₁ h₂
    have e₁ := List.IsChain.iterate_eq_of_apply_eq hchain i h₁
    have e₂ := List.IsChain.iterate_eq_of_apply_eq hrotchain i h₂
    have hz : (arc[0] :: (suf ++ pre))[0] = arc[0] := rfl
    rw [← e₁, ← e₂, hz]
  obtain ⟨interior, hinterior⟩ :=
    exists_append_of_getElem_eq arc (arc[0] :: (suf ++ pre)) hlen2 hgetElem
  refine ⟨pre.length, interior, ?_⟩
  rw [hrot]
  exact hinterior

/-! ## Recognising a run inside the boundary walk -/

/-- A stretch of the boundary walk along which the face rotation never leaves
the boundary is chained by the face rotation itself. -/
theorem isChain_facePerm_of_boundaryStep
    {faces : Finset Delta.toCombMap.Face}
    {arc : List Delta.toCombMap.Dart}
    (hchain : arc.IsChain (BoundaryStep Delta faces))
    (hnext : ∀ d ∈ arc, ∀ e ∈ arc, BoundaryStep Delta faces d e →
      IsBoundaryDart Delta faces (Delta.toCombMap.facePerm d)) :
    arc.IsChain fun d e => Delta.toCombMap.facePerm d = e := by
  refine List.IsChain.imp_of_mem_imp ?_ hchain
  intro a b ha hb hab
  exact (boundaryStep_eq_facePerm hab (hnext a ha b hb hab)).symm

/-- Every dart of a face-rotation chain lies on the face of its first dart. -/
private theorem faceOf_const_aux :
    ∀ (tail : List Delta.toCombMap.Dart) (a : Delta.toCombMap.Dart),
      (a :: tail).IsChain (fun d e => Delta.toCombMap.facePerm d = e) →
      ∀ d ∈ a :: tail,
        Delta.toCombMap.faceOf d = Delta.toCombMap.faceOf a
  | [], a, _ => by
      intro d hd
      rcases List.mem_cons.mp hd with hd | hd
      · rw [hd]
      · simp at hd
  | b :: tail, a, hchain => by
      intro d hd
      have hab : Delta.toCombMap.facePerm a = b :=
        (List.isChain_cons_cons.mp hchain).1
      have htail : (b :: tail).IsChain
          (fun d e => Delta.toCombMap.facePerm d = e) :=
        (List.isChain_cons_cons.mp hchain).2
      have hface : Delta.toCombMap.faceOf b = Delta.toCombMap.faceOf a := by
        rw [← hab]
        exact Delta.toCombMap.faceOf_facePerm a
      rcases List.mem_cons.mp hd with hd | hd
      · rw [hd]
      · rw [faceOf_const_aux tail b htail d hd, hface]

/-- A face-rotation chain lies on a single face. -/
theorem faceOf_eq_head_of_isChain_facePerm
    {arc : List Delta.toCombMap.Dart} (harc : arc ≠ [])
    (hchain : arc.IsChain fun d e => Delta.toCombMap.facePerm d = e) :
    ∀ d ∈ arc,
      Delta.toCombMap.faceOf d = Delta.toCombMap.faceOf (arc.head harc) := by
  cases arc with
  | nil => exact (harc rfl).elim
  | cons a tail => exact faceOf_const_aux tail a hchain

/-- The face-boundary datum of a planar ear, from the arc alone.  A producer
of the ear only has to exhibit a duplicate-free nonempty stretch of the
boundary walk which never leaves its face; the base shift and the rest of the
face boundary are then automatic. -/
theorem exists_faceRotation_of_run
    {faces : Finset Delta.toCombMap.Face}
    {face : Delta.toCombMap.Face}
    {arc : List Delta.toCombMap.Dart}
    (harc : arc ≠ []) (hnodup : arc.Nodup)
    (hchain : arc.IsChain (BoundaryStep Delta faces))
    (hnext : ∀ d ∈ arc, ∀ e ∈ arc, BoundaryStep Delta faces d e →
      IsBoundaryDart Delta faces (Delta.toCombMap.facePerm d))
    (hface : Delta.toCombMap.faceOf (arc.head harc) = face) :
    ∃ (k : ℕ) (interior : List Delta.toCombMap.Dart),
      (Delta.faceBoundary face).darts.rotate k = arc ++ interior := by
  have hchain' := isChain_facePerm_of_boundaryStep hchain hnext
  have hface' : ∀ d ∈ arc, Delta.toCombMap.faceOf d = face := by
    intro d hd
    rw [faceOf_eq_head_of_isChain_facePerm harc hchain' d hd]
    exact hface
  exact exists_faceBoundary_rotate_eq_append harc hnodup hface' hchain'

end Embedded
end VanKampen
end GGT
end GroupApproximation
