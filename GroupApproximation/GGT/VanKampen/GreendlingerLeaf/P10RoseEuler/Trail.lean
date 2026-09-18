import GroupApproximation.GGT.VanKampen.ClosedWalkPinchSplit
import GroupApproximation.Meta.AxiomGuard

/-!
# Closed trails of a list with start and end labels

Generic tools for the Euler re-listing (lane gl-p10-06).  A list `l : List α` with a start label
`s : α → V` and an end label `t : α → V` is a *closed trail* when it is nonempty, each entry ends
where the next one starts, and the last entry ends where the first one starts.  With
`s = M.vertexOf` and `t = fun d => M.vertexOf (M.alpha d)` this is `IsClosedDartWalk M` by
definition.

* `IsClosedTrail.append_comm`: rotations keep closed trails closed
  (`ClosedWalkFaceColouring.closedChain_append_comm`).
* `IsClosedTrail.exists_rotation_head`: rotate a given entry to the front.
* `IsClosedTrail.exists_start_eq_end`: every end label is the start label of some entry.
* `IsClosedTrail.append`: two closed trails, the first ending where the second starts, concatenate
  to a closed trail.
* `IsClosedTrail.splice`: insert a closed trail `C` after the block `A` of a closed trail `A ++ B`
  (rotate to `B ++ A`, append `C`, rotate back).
* `IsClosedTrail.join`: two closed trails with a common start label merge into one closed trail
  that is a permutation of their concatenation.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseEuler

open GroupApproximation.GGT.VanKampen.ClosedWalkFaceColouring

section Generic

variable {α V : Type*} {s t : α → V}

/-- **A closed trail.**  A nonempty list in which each entry ends (label `t`) where the next one
starts (label `s`), and the last entry ends where the first one starts. -/
def IsClosedTrail (s t : α → V) (l : List α) : Prop :=
  ∃ hne : l ≠ [], l.IsChain (fun a b => t a = s b) ∧ t (l.getLast hne) = s (l.head hne)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseEuler.IsClosedTrail

/-- A closed trail is nonempty. -/
theorem IsClosedTrail.ne_nil {l : List α} (h : IsClosedTrail s t l) : l ≠ [] := by
  obtain ⟨hne, _, _⟩ := h
  exact hne

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseEuler.IsClosedTrail.ne_nil

/-- A closed trail is a nonempty closed chain. -/
theorem isClosedTrail_iff_closedChain {l : List α} :
    IsClosedTrail s t l ↔ l ≠ [] ∧ ClosedChain (fun a b => t a = s b) l := by
  constructor
  · rintro ⟨hne, hc, hclose⟩
    exact ⟨hne, (closedChain_iff hne).mpr ⟨hc, hclose⟩⟩
  · rintro ⟨hne, h⟩
    obtain ⟨hc, hclose⟩ := (closedChain_iff hne).mp h
    exact ⟨hne, hc, hclose⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseEuler.isClosedTrail_iff_closedChain

/-- **Rotating a closed trail keeps it closed.** -/
theorem IsClosedTrail.append_comm {P Q : List α} (h : IsClosedTrail s t (P ++ Q)) :
    IsClosedTrail s t (Q ++ P) := by
  obtain ⟨hne, hcc⟩ := isClosedTrail_iff_closedChain.mp h
  refine isClosedTrail_iff_closedChain.mpr ⟨fun h0 => hne ?_, closedChain_append_comm hcc⟩
  obtain ⟨hQ, hP⟩ := List.append_eq_nil_iff.mp h0
  rw [hP, hQ, List.nil_append]

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseEuler.IsClosedTrail.append_comm

/-- **Rotating an entry to the front.** -/
theorem IsClosedTrail.exists_rotation_head {l : List α} (h : IsClosedTrail s t l) {c : α}
    (hc : c ∈ l) :
    ∃ l' : List α, ∃ hne : l' ≠ [], l'.Perm l ∧ IsClosedTrail s t l' ∧ l'.head hne = c := by
  obtain ⟨P, Q, rfl⟩ := List.append_of_mem hc
  have hne : (c :: Q) ++ P ≠ [] := List.cons_ne_nil c (Q ++ P)
  exact ⟨(c :: Q) ++ P, hne, List.perm_append_comm, h.append_comm, rfl⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseEuler.IsClosedTrail.exists_rotation_head

/-- **Every end label of a closed trail is a start label.**  The successor of `d` starts where `d`
ends; the last entry ends where the first starts. -/
theorem IsClosedTrail.exists_start_eq_end {l : List α} (h : IsClosedTrail s t l) {d : α}
    (hd : d ∈ l) : ∃ c ∈ l, s c = t d := by
  obtain ⟨hne, hc, hclose⟩ := h
  obtain ⟨P, Q, rfl⟩ := List.append_of_mem hd
  cases Q with
  | nil =>
    refine ⟨(P ++ [d]).head hne, List.head_mem hne, ?_⟩
    have h1 : (P ++ [d]).getLast hne = d :=
      List.getLast_append_of_ne_nil hne (List.cons_ne_nil d [])
    rw [h1] at hclose
    exact hclose.symm
  | cons c Q =>
    refine ⟨c, by simp, ?_⟩
    have h2 : (d :: c :: Q).IsChain (fun a b => t a = s b) := (List.isChain_append.mp hc).2.1
    exact Eq.symm (List.isChain_cons_cons.mp h2).1

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseEuler.IsClosedTrail.exists_start_eq_end

/-- **Concatenating two closed trails at a common vertex.** -/
theorem IsClosedTrail.append {A C : List α} (hA : IsClosedTrail s t A)
    (hC : IsClosedTrail s t C) (hA0 : A ≠ []) (hC0 : C ≠ [])
    (hv : t (A.getLast hA0) = s (C.head hC0)) : IsClosedTrail s t (A ++ C) := by
  obtain ⟨_, hAc, hAclose⟩ := hA
  obtain ⟨_, hCc, hCclose⟩ := hC
  have hne : A ++ C ≠ [] := fun h => hA0 (List.append_eq_nil_iff.mp h).1
  refine ⟨hne, List.IsChain.append hAc hCc ?_, ?_⟩
  · intro x hx y hy
    simp only [List.getLast?_eq_some_getLast hA0, Option.mem_def, Option.some.injEq] at hx
    simp only [List.head?_eq_some_head hC0, Option.mem_def, Option.some.injEq] at hy
    subst hx hy
    exact hv
  · rw [List.getLast_append_of_ne_nil hne hC0, List.head_append_of_ne_nil hA0, hCclose, ← hv]
    exact hAclose

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseEuler.IsClosedTrail.append

/-- **Splicing a closed trail into a closed trail.**  If `A ++ B` and `C` are closed trails and
`A` ends where `C` starts, then `A ++ C ++ B` is a closed trail. -/
theorem IsClosedTrail.splice {A B C : List α} (hAB : IsClosedTrail s t (A ++ B))
    (hC : IsClosedTrail s t C) (hA : A ≠ []) (hC0 : C ≠ [])
    (hv : t (A.getLast hA) = s (C.head hC0)) : IsClosedTrail s t (A ++ C ++ B) := by
  have hBA : IsClosedTrail s t (B ++ A) := hAB.append_comm
  have hBA0 : B ++ A ≠ [] := fun h => hA (List.append_eq_nil_iff.mp h).2
  have hv' : t ((B ++ A).getLast hBA0) = s (C.head hC0) := by
    rw [List.getLast_append_of_ne_nil hBA0 hA]
    exact hv
  have h3 : IsClosedTrail s t (B ++ A ++ C) := hBA.append hC hBA0 hC0 hv'
  have h4 : IsClosedTrail s t (B ++ (A ++ C)) := by
    rw [← List.append_assoc]
    exact h3
  exact h4.append_comm

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseEuler.IsClosedTrail.splice

/-- **Merging two closed trails through a common start label.** -/
theorem IsClosedTrail.join {W C : List α} (hW : IsClosedTrail s t W) (hC : IsClosedTrail s t C)
    {w c : α} (hw : w ∈ W) (hc : c ∈ C) (hwc : s w = s c) :
    ∃ J : List α, J.Perm (W ++ C) ∧ IsClosedTrail s t J := by
  obtain ⟨W', hW'0, hW'perm, hW', hW'head⟩ := hW.exists_rotation_head hw
  obtain ⟨C', hC'0, hC'perm, hC', hC'head⟩ := hC.exists_rotation_head hc
  refine ⟨W' ++ C', hW'perm.append hC'perm, hW'.append hC' hW'0 hC'0 ?_⟩
  obtain ⟨_, _, hclose⟩ := hW'
  rw [hclose, hW'head, hC'head]
  exact hwc

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseEuler.IsClosedTrail.join

end Generic

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseEuler
