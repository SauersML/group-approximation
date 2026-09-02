import GroupApproximation.GGT.VanKampen.FaceSetBoundaryPeeling

/-!
# Rotation of a selected-face boundary

The boundary stored by `Estimating.FaceSetBoundary` is a cyclic list with an
arbitrary base dart.  This file proves that changing that base by `List.rotate`
preserves every field of the record.  The chain proof is the elementary cyclic
chain argument: the old chain supplies the edge across the cut and the old
closing relation supplies the new edge from the old end to the old beginning.
The final lemmas expose a basepoint at any selected boundary dart.  They are
the map-level transport used by face peeling; no extra topological certificate
is introduced.
-/

namespace GroupApproximation
namespace GGT
namespace VanKampen

open GroupApproximation.HullSC

universe u w v

namespace Embedded

variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (GGT.RelLetter G Lambda))}
  {Delta : DiscDiagram.{u, w, v} W}

noncomputable local instance faceDecidableEqRotation :
    DecidableEq Delta.toCombMap.Face := Classical.decEq _

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

private theorem head_append_of_left_ne_nil
    {α : Type*} {left right : List α} (hleft : left ≠ []) :
    (left ++ right).head (List.append_ne_nil_of_left_ne_nil hleft right) =
      left.head hleft := by
  cases left with
  | nil => exact (hleft rfl).elim
  | cons a tail => rfl

private theorem head_eq_of_mem_head?
    {α : Type*} {cycle : List α} (hne : cycle ≠ [])
    {d : α} (hd : d ∈ cycle.head?) : d = cycle.head hne := by
  cases cycle with
  | nil => exact (hne rfl).elim
  | cons a tail =>
      have hmem : a = d := by
        simpa only [List.head?, Option.mem_def, Option.some_inj] using hd
      exact hmem.symm

private theorem head_congr
    {α : Type*} {left right : List α}
    (hleft : left ≠ []) (hright : right ≠ []) (heq : left = right) :
    left.head hleft = right.head hright := by
  subst right
  rfl

private theorem isChain_rotate_of_isChain_closes
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
  have hsplit : cycle.take k ++ cycle.drop k = cycle :=
    List.take_append_drop k cycle
  have hsplit_chain : (cycle.take k ++ cycle.drop k).IsChain R := by
    rw [hsplit]
    exact hchain
  have hcut : R ((cycle.take k).getLast hktake)
      ((cycle.drop k).head hkdrop) :=
    hsplit_chain.rel_getLast_head_of_append hktake hkdrop
  have hrot_chain : (cycle.drop k ++ cycle.take k).IsChain R := by
    apply List.IsChain.append (hchain.drop k) (hchain.take k)
    intro x hx y hy
    have hxlast : x = (cycle.drop k).getLast hkdrop := by
      have hx' := List.mem_getLast?_eq_getLast hx
      obtain ⟨hxproof, hxEq⟩ := hx'
      exact hxEq
    have hyhead : y = (cycle.take k).head hktake :=
      head_eq_of_mem_head? hktake hy
    rw [hxlast, hyhead, getLast_drop_eq_getLast hne hkdrop,
      head_take_eq_head hne hktake]
    exact hclose
  rw [hrot]
  exact hrot_chain

private theorem isChain_rotate_closing
    {α : Type*} {R : α → α → Prop} {cycle : List α}
    (hne : cycle ≠ []) (hchain : cycle.IsChain R)
    (hclose : R (cycle.getLast hne) (cycle.head hne)) (n : ℕ)
    (hnrot : cycle.rotate n ≠ []) :
    R ((cycle.rotate n).getLast hnrot) ((cycle.rotate n).head hnrot) := by
  have hlen : 0 < cycle.length := List.length_pos_of_ne_nil hne
  let k : ℕ := n % cycle.length
  have hrot : cycle.rotate n = cycle.drop k ++ cycle.take k := by
    dsimp [k]
    exact List.rotate_eq_drop_append_take_mod
  by_cases hkzero : k = 0
  · have hleft : cycle.drop k ≠ [] := by
      rw [hkzero]
      simpa using hne
    have happend : cycle.drop k ++ cycle.take k ≠ [] :=
      List.append_ne_nil_of_left_ne_nil hleft _
    have hrel : R ((cycle.drop k ++ cycle.take k).getLast happend)
        ((cycle.drop k ++ cycle.take k).head happend) := by
      have hzero : cycle.drop k ++ cycle.take k = cycle := by
        rw [hkzero]
        simp
      have hlast0 : (cycle.drop k ++ cycle.take k).getLast happend =
          cycle.getLast hne := List.getLast_congr happend hne hzero
      have hhead0 : (cycle.drop k ++ cycle.take k).head happend =
          cycle.head hne := head_congr happend hne hzero
      rw [hlast0, hhead0]
      exact hclose
    have hlast0 : (cycle.rotate n).getLast hnrot =
        (cycle.drop k ++ cycle.take k).getLast happend :=
      List.getLast_congr hnrot happend hrot
    have hhead0 : (cycle.rotate n).head hnrot =
        (cycle.drop k ++ cycle.take k).head happend :=
      head_congr hnrot happend hrot
    rw [hlast0, hhead0]
    exact hrel
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
  have hsplit : cycle.take k ++ cycle.drop k = cycle :=
    List.take_append_drop k cycle
  have hsplit_chain : (cycle.take k ++ cycle.drop k).IsChain R := by
    rw [hsplit]
    exact hchain
  have hcut : R ((cycle.take k).getLast hktake)
      ((cycle.drop k).head hkdrop) :=
    hsplit_chain.rel_getLast_head_of_append hktake hkdrop
  have hlast :
      (cycle.drop k ++ cycle.take k).getLast
          (List.append_ne_nil_of_right_ne_nil _ hktake) =
        (cycle.take k).getLast hktake := by
    exact List.getLast_append_of_right_ne_nil _ _ hktake
  have hhead :
      (cycle.drop k ++ cycle.take k).head
          (List.append_ne_nil_of_left_ne_nil hkdrop _) =
        (cycle.drop k).head hkdrop := by
    exact head_append_of_left_ne_nil hkdrop
  have happend : cycle.drop k ++ cycle.take k ≠ [] :=
    List.append_ne_nil_of_right_ne_nil _ hktake
  have hrel : R ((cycle.drop k ++ cycle.take k).getLast happend)
      ((cycle.drop k ++ cycle.take k).head happend) := by
    rw [hlast, hhead]
    exact hcut
  have hlast0 : (cycle.rotate n).getLast hnrot =
      (cycle.drop k ++ cycle.take k).getLast happend :=
    List.getLast_congr hnrot happend hrot
  have hhead0 : (cycle.rotate n).head hnrot =
      (cycle.drop k ++ cycle.take k).head happend :=
    head_congr hnrot happend hrot
  rw [hlast0, hhead0]
  exact hrel

/-! ## Rotation of the record -/

/-- Rotate the chosen base dart of a `FaceSetBoundary` cycle. -/
def FaceSetBoundary.rotate
    {faces : Finset Delta.toCombMap.Face}
    (boundary : FaceSetBoundary Delta faces) (k : ℕ) :
    FaceSetBoundary Delta faces where
  faces_nonempty := boundary.faces_nonempty
  all_gCells := boundary.all_gCells
  cycle := boundary.cycle.rotate k
  cycle_nonempty := by
    intro h
    apply boundary.cycle_nonempty
    exact List.rotate_eq_nil_iff.mp h
  cycle_nodup := (List.nodup_rotate.mpr boundary.cycle_nodup)
  cycle_mem_iff := by
    intro d
    rw [List.mem_rotate]
    exact boundary.cycle_mem_iff d
  cycle_chain := by
    exact isChain_rotate_of_isChain_closes boundary.cycle_nonempty
      boundary.cycle_chain boundary.cycle_closes k
  cycle_closes := by
    have hrotne : boundary.cycle.rotate k ≠ [] := by
      intro h
      apply boundary.cycle_nonempty
      exact List.rotate_eq_nil_iff.mp h
    exact isChain_rotate_closing boundary.cycle_nonempty boundary.cycle_chain
      boundary.cycle_closes k hrotne

@[simp] theorem FaceSetBoundary.rotate_cycle
    {faces : Finset Delta.toCombMap.Face}
    (boundary : FaceSetBoundary Delta faces) (k : ℕ) :
    (boundary.rotate k).cycle = boundary.cycle.rotate k := rfl

theorem FaceSetBoundary.rotate_mem_iff
    {faces : Finset Delta.toCombMap.Face}
    (boundary : FaceSetBoundary Delta faces) (k : ℕ)
    (d : Delta.toCombMap.Dart) :
    d ∈ (boundary.rotate k).cycle ↔ d ∈ boundary.cycle := by
  rw [FaceSetBoundary.rotate_cycle, List.mem_rotate]

/-! ## Basepoint exposure -/

private theorem exists_append_cons_of_mem
    {α : Type*} {d : α} : ∀ {cycle : List α}, d ∈ cycle →
      ∃ before after : List α, cycle = before ++ d :: after
  | [], h => (by simp at h)
  | a :: tail, h => by
      by_cases had : a = d
      · subst a
        exact ⟨[], tail, rfl⟩
      · have htail : d ∈ tail := by
          exact (List.mem_cons.mp h).resolve_left (fun hda => had hda.symm)
        obtain ⟨before, after, hsplit⟩ := exists_append_cons_of_mem htail
        refine ⟨a :: before, after, ?_⟩
        rw [hsplit]
        simp only [List.cons_append]

/-- A boundary with a specified base dart, given an explicit split of its
cycle at that dart. -/
def FaceSetBoundary.ofDart
    {faces : Finset Delta.toCombMap.Face}
    (boundary : FaceSetBoundary Delta faces)
    (d : Delta.toCombMap.Dart)
    (before after : List Delta.toCombMap.Dart)
    (_hsplit : boundary.cycle = before ++ d :: after) :
    FaceSetBoundary Delta faces :=
  boundary.rotate before.length

theorem FaceSetBoundary.ofDart_cycle_eq
    {faces : Finset Delta.toCombMap.Face}
    (boundary : FaceSetBoundary Delta faces)
    (d : Delta.toCombMap.Dart)
    (before after : List Delta.toCombMap.Dart)
    (hsplit : boundary.cycle = before ++ d :: after) :
    (boundary.ofDart d before after hsplit).cycle =
      (before ++ d :: after).drop before.length ++
        (before ++ d :: after).take before.length := by
  change boundary.cycle.rotate before.length = _
  rw [hsplit, List.rotate_eq_drop_append_take]
  exact (by
    simp only [List.length_append, List.length_cons]
    omega)

theorem FaceSetBoundary.exists_ofDart
    {faces : Finset Delta.toCombMap.Face}
    (boundary : FaceSetBoundary Delta faces)
    (d : Delta.toCombMap.Dart)
    (hd : IsBoundaryDart Delta faces d) :
    ∃ before after : List Delta.toCombMap.Dart,
      boundary.cycle = before ++ d :: after ∧
        (boundary.rotate before.length).cycle =
          boundary.cycle.rotate before.length := by
  have hmem : d ∈ boundary.cycle :=
    (boundary.cycle_mem_iff d).2 hd
  obtain ⟨before, after, hsplit⟩ := exists_append_cons_of_mem hmem
  refine ⟨before, after, hsplit, ?_⟩
  rfl

/-! ## Small model checks -/

theorem rotate_one_face_model
    {face : Delta.toCombMap.Face}
    {boundary : FaceSetBoundary Delta ({face} : Finset Delta.toCombMap.Face)}
    (k : ℕ) :
    (boundary.rotate k).cycle = boundary.cycle.rotate k := rfl

theorem rotate_two_face_model
    {f₁ f₂ : Delta.toCombMap.Face}
    {boundary : FaceSetBoundary Delta ({f₁, f₂} : Finset Delta.toCombMap.Face)}
    (k : ℕ) :
    (boundary.rotate k).cycle = boundary.cycle.rotate k := rfl

theorem rotate_four_face_model
    {f₁ f₂ f₃ f₄ : Delta.toCombMap.Face}
    {boundary : FaceSetBoundary Delta ({f₁, f₂, f₃, f₄} : Finset Delta.toCombMap.Face)}
    (k : ℕ) :
    (boundary.rotate k).cycle = boundary.cycle.rotate k := rfl

end Embedded
end VanKampen
end GGT
end GroupApproximation
