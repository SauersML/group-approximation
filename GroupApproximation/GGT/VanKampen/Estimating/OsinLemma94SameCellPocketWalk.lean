import GroupApproximation.GGT.VanKampen.ClosedWalkPinchSplit
import GroupApproximation.GGT.VanKampen.FaceBoundaryRotation
import GroupApproximation.GGT.VanKampen.FaceShelling
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketWalkChain
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixO52Values
import GroupApproximation.Meta.AxiomGuard

/-!
# The pocket walks of Lemma 9.4, Case 1, across one relator cell, are closed walks

Osin (math/0411039v3, §9), Lemma 9.4, Case 1, for a backwards connector pair whose source and
target sides lie across one relator cell `Π` (`OsinLemma94CaseOneSameCellStatement`).  Some
rotation of the face walk reads `X q⁻¹ Y p⁻¹` (`osinLemma94CaseOneWalk_sameCell`), and some
rotation of the carrier of `Π` reads `q B p A`.  Then `X` and `B` run between the start of `p` and
the end of `q`, in opposite directions, and so do `Y` and `A` between the end of `p` and the start
of `q`.  So the pocket walks `invDarts X ++ invDarts B` and `invDarts Y ++ invDarts A` are closed
dart walks (`SameCellPocketWalk.isClosedDartWalk_X`, `_Y`), whenever they are nonempty.  Empty
windows are allowed.

* `IsWalkFromTo`: a dart list is a walk between two vertices; an empty list joins a vertex to
  itself.  Walks append, reverse, split at any position, and have unique endpoints when nonempty.
* `exists_isWalkFromTo_faceBoundary_rotate`: a rotated face traversal is a closed walk.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121, Hull's small cancellation theorem, through Osin's
Lemma 9.4, Case 1); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

namespace SameCellPocketWalk

open Embedded

section Walk

variable {M : CombMap.{v}}

/-- **A dart list is a walk from `x` to `y`**: consecutive darts meet, the first dart starts at
`x`, the last dart ends at `y`, and an empty list has `x = y`. -/
def IsWalkFromTo (M : CombMap.{v}) (l : List M.Dart) (x y : M.Vertex) : Prop :=
  l.IsChain (fun d e => M.vertexOf (M.alpha d) = M.vertexOf e) ∧
    (∀ a ∈ l.head?, M.vertexOf a = x) ∧ (∀ a ∈ l.getLast?, M.vertexOf (M.alpha a) = y) ∧
      (l = [] → x = y)

theorem isWalkFromTo_nil (x : M.Vertex) : IsWalkFromTo M [] x x :=
  ⟨List.IsChain.nil, fun _ h => by simp at h, fun _ h => by simp at h, fun _ => rfl⟩

theorem mem_head?_append_of_mem {l₁ l₂ : List M.Dart} {a : M.Dart} (ha : a ∈ l₁.head?) :
    a ∈ (l₁ ++ l₂).head? := by
  rw [Option.mem_def] at ha ⊢
  rw [List.head?_append, ha, Option.some_or]

theorem mem_getLast?_append_of_mem {l₁ l₂ : List M.Dart} {a : M.Dart} (ha : a ∈ l₂.getLast?) :
    a ∈ (l₁ ++ l₂).getLast? := by
  rw [Option.mem_def] at ha ⊢
  rw [List.getLast?_append, ha, Option.some_or]

/-- **Walks append.** -/
theorem IsWalkFromTo.append {l₁ l₂ : List M.Dart} {x y z : M.Vertex}
    (h₁ : IsWalkFromTo M l₁ x y) (h₂ : IsWalkFromTo M l₂ y z) :
    IsWalkFromTo M (l₁ ++ l₂) x z := by
  by_cases hl₁ : l₁ = []
  · subst hl₁
    obtain rfl := h₁.2.2.2 rfl
    simpa using h₂
  by_cases hl₂ : l₂ = []
  · subst hl₂
    obtain rfl := h₂.2.2.2 rfl
    simpa using h₁
  refine ⟨List.isChain_append.mpr ⟨h₁.1, h₂.1, fun a ha b hb =>
    (h₁.2.2.1 a ha).trans (h₂.2.1 b hb).symm⟩, fun a ha => ?_, fun a ha => ?_,
    fun h => absurd (List.append_eq_nil_iff.mp h).1 hl₁⟩
  · rw [Option.mem_def, List.head?_append] at ha
    cases hg : l₁.head? with
    | none => exact absurd (List.head?_eq_none_iff.mp hg) hl₁
    | some b =>
      rw [hg, Option.some_or] at ha
      exact h₁.2.1 a (by rw [hg, Option.mem_def, ha])
  · rw [Option.mem_def, List.getLast?_append] at ha
    cases hg : l₂.getLast? with
    | none => exact absurd (List.getLast?_eq_none_iff.mp hg) hl₂
    | some b =>
      rw [hg, Option.some_or] at ha
      exact h₂.2.2.1 a (by rw [hg, Option.mem_def, ha])

/-- **Walks reverse.** -/
theorem IsWalkFromTo.reverse_map {l : List M.Dart} {x y : M.Vertex} (h : IsWalkFromTo M l x y) :
    IsWalkFromTo M (l.reverse.map M.alpha) y x := by
  refine ⟨?_, fun a ha => ?_, fun a ha => ?_, fun hnil => (h.2.2.2 (by simpa using hnil)).symm⟩
  · rw [List.isChain_map, List.isChain_reverse]
    refine h.1.imp fun a b hab => ?_
    show M.vertexOf (M.alpha (M.alpha b)) = M.vertexOf (M.alpha a)
    rw [M.alpha_involutive b]
    exact hab.symm
  · rw [List.head?_map, List.head?_reverse, Option.mem_def, Option.map_eq_some_iff] at ha
    obtain ⟨a', ha', rfl⟩ := ha
    exact h.2.2.1 a' (Option.mem_def.mpr ha')
  · rw [List.getLast?_map, List.getLast?_reverse, Option.mem_def, Option.map_eq_some_iff] at ha
    obtain ⟨a', ha', rfl⟩ := ha
    rw [M.alpha_involutive a']
    exact h.2.1 a' (Option.mem_def.mpr ha')

/-- **Walks split** at any position. -/
theorem IsWalkFromTo.exists_split {l₁ l₂ : List M.Dart} {x z : M.Vertex}
    (h : IsWalkFromTo M (l₁ ++ l₂) x z) :
    ∃ y, IsWalkFromTo M l₁ x y ∧ IsWalkFromTo M l₂ y z := by
  by_cases hl₁ : l₁ = []
  · subst hl₁
    exact ⟨x, isWalkFromTo_nil x, by simpa using h⟩
  have hlast : l₁.getLast hl₁ ∈ l₁.getLast? := by
    rw [List.getLast?_eq_some_getLast hl₁, Option.mem_def]
  refine ⟨M.vertexOf (M.alpha (l₁.getLast hl₁)),
    ⟨(List.isChain_append.mp h.1).1, fun a ha => h.2.1 a (mem_head?_append_of_mem ha),
      fun a ha => ?_, fun hnil => absurd hnil hl₁⟩,
    ⟨(List.isChain_append.mp h.1).2.1,
      fun b hb => ((List.isChain_append.mp h.1).2.2 _ hlast b hb).symm,
      fun a ha => h.2.2.1 a (mem_getLast?_append_of_mem ha), fun hnil => ?_⟩⟩
  · rw [List.getLast?_eq_some_getLast hl₁, Option.mem_def, Option.some.injEq] at ha
    rw [ha]
  · subst hnil
    exact h.2.2.1 _ (by rw [List.append_nil]; exact hlast)

/-- **A nonempty walk has unique endpoints.** -/
theorem IsWalkFromTo.eq_of_ne_nil {l : List M.Dart} {x y x' y' : M.Vertex}
    (h : IsWalkFromTo M l x y) (h' : IsWalkFromTo M l x' y') (hne : l ≠ []) :
    x = x' ∧ y = y' := by
  have hh : l.head hne ∈ l.head? := by rw [List.head?_eq_some_head hne, Option.mem_def]
  have hl : l.getLast hne ∈ l.getLast? := by
    rw [List.getLast?_eq_some_getLast hne, Option.mem_def]
  exact ⟨(h.2.1 _ hh).symm.trans (h'.2.1 _ hh), (h.2.2.1 _ hl).symm.trans (h'.2.2.1 _ hl)⟩

/-- **A nonempty walk from a vertex to itself is a closed dart walk.** -/
theorem IsWalkFromTo.isClosedDartWalk {l : List M.Dart} {x : M.Vertex}
    (h : IsWalkFromTo M l x x) (hne : l ≠ []) : IsClosedDartWalk M l :=
  ⟨hne, h.1, (h.2.2.1 _ (by rw [List.getLast?_eq_some_getLast hne, Option.mem_def])).trans
    (h.2.1 _ (by rw [List.head?_eq_some_head hne, Option.mem_def])).symm⟩

/-- A chained list that closes up is a walk from its first vertex to itself. -/
theorem isWalkFromTo_of_isChain_closes {l : List M.Dart} (hne : l ≠ [])
    (hchain : l.IsChain fun d e => M.vertexOf (M.alpha d) = M.vertexOf e)
    (hcloses : ∀ a ∈ l.getLast?, ∀ b ∈ l.head?, M.vertexOf (M.alpha a) = M.vertexOf b) :
    IsWalkFromTo M l (M.vertexOf (l.head hne)) (M.vertexOf (l.head hne)) := by
  have hh : l.head hne ∈ l.head? := by rw [List.head?_eq_some_head hne, Option.mem_def]
  refine ⟨hchain, fun a ha => ?_, fun a ha => hcloses a ha _ hh, fun h => absurd h hne⟩
  rw [List.head?_eq_some_head hne, Option.mem_def, Option.some.injEq] at ha
  rw [ha]

end Walk

section Pocket

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {Delta : DiscDiagram.{u, w, v} W}

/-- **A rotated face traversal is a closed walk.** -/
theorem exists_isWalkFromTo_faceBoundary_rotate (f : Delta.toCombMap.Face) (r : ℕ) :
    ∃ x, IsWalkFromTo Delta.toCombMap ((Delta.faceBoundary f).darts.rotate r) x x := by
  obtain ⟨hchain, hcloses⟩ := isChain_closes_of_faceBoundary ((Delta.faceBoundary f).rotate r)
  exact ⟨_, isWalkFromTo_of_isChain_closes ((Delta.faceBoundary f).rotate r).nonempty hchain
    hcloses⟩

/-- **The endpoints of the four windows.**  With the face walk `X q⁻¹ Y p⁻¹` and the carrier
`q B p A`: `X` runs from `x` to `y`, `B` from `y` to `x`, `Y` from `y'` to `x'`, and `A` from `x'`
to `y'`. -/
theorem exists_window_walks {f : Delta.toCombMap.Face} {j : Fin Delta.rCellCount}
    (sourceArc targetArc : CyclicArc (cellDarts Delta j)) {X Y : List Delta.toCombMap.Dart}
    {r : ℕ} (htrav : (Delta.faceBoundary f).darts.rotate r =
      X ++ targetArc.reverseDarts ++ Y ++ sourceArc.reverseDarts)
    {B A : List Delta.toCombMap.Dart} {n : ℕ}
    (hPi : (cellDarts Delta j).rotate n = targetArc.darts ++ B ++ sourceArc.darts ++ A)
    (hs : 0 < sourceArc.length) (ht : 0 < targetArc.length) :
    ∃ x y x' y' : Delta.toCombMap.Vertex,
      IsWalkFromTo Delta.toCombMap X x y ∧ IsWalkFromTo Delta.toCombMap B y x ∧
        IsWalkFromTo Delta.toCombMap Y y' x' ∧ IsWalkFromTo Delta.toCombMap A x' y' := by
  obtain ⟨x₀, hF⟩ := exists_isWalkFromTo_faceBoundary_rotate (Delta := Delta) f r
  rw [htrav] at hF
  obtain ⟨v₃, hF₁, hP'⟩ := hF.exists_split
  obtain ⟨v₂, hF₂, hY⟩ := hF₁.exists_split
  obtain ⟨v₁, hX, hQ'⟩ := hF₂.exists_split
  have hK : ∃ u, IsWalkFromTo Delta.toCombMap ((cellDarts Delta j).rotate n) u u :=
    exists_isWalkFromTo_faceBoundary_rotate (cell Delta j).face n
  obtain ⟨u₀, hK⟩ := hK
  rw [hPi] at hK
  obtain ⟨w₃, hK₁, hA⟩ := hK.exists_split
  obtain ⟨w₂, hK₂, hP⟩ := hK₁.exists_split
  obtain ⟨w₁, hQ, hB⟩ := hK₂.exists_split
  have hQ'' : IsWalkFromTo Delta.toCombMap targetArc.darts v₂ v₁ := by
    have h := hQ'.reverse_map
    have e : targetArc.reverseDarts.reverse.map Delta.toCombMap.alpha = targetArc.darts :=
      invDarts_invDarts targetArc.darts
    rwa [e] at h
  have hP'' : IsWalkFromTo Delta.toCombMap sourceArc.darts x₀ v₃ := by
    have h := hP'.reverse_map
    have e : sourceArc.reverseDarts.reverse.map Delta.toCombMap.alpha = sourceArc.darts :=
      invDarts_invDarts sourceArc.darts
    rwa [e] at h
  obtain ⟨hu, hw₁⟩ := hQ.eq_of_ne_nil hQ'' (targetArc.darts_ne_nil_of_length_pos ht)
  obtain ⟨hw₂, hw₃⟩ := hP.eq_of_ne_nil hP'' (sourceArc.darts_ne_nil_of_length_pos hs)
  subst hu hw₁ hw₂ hw₃
  exact ⟨w₂, w₁, w₃, u₀, hX, hB, hY, hA⟩

/-- **The X-pocket walk is a closed dart walk.** -/
theorem isClosedDartWalk_X {f : Delta.toCombMap.Face} {j : Fin Delta.rCellCount}
    (sourceArc targetArc : CyclicArc (cellDarts Delta j)) {X Y : List Delta.toCombMap.Dart}
    {r : ℕ} (htrav : (Delta.faceBoundary f).darts.rotate r =
      X ++ targetArc.reverseDarts ++ Y ++ sourceArc.reverseDarts)
    {B A : List Delta.toCombMap.Dart} {n : ℕ}
    (hPi : (cellDarts Delta j).rotate n = targetArc.darts ++ B ++ sourceArc.darts ++ A)
    (hs : 0 < sourceArc.length) (ht : 0 < targetArc.length) (hne : X ++ B ≠ []) :
    IsClosedDartWalk Delta.toCombMap (invDarts Delta X ++ invDarts Delta B) := by
  obtain ⟨x, y, -, -, hX, hB, -, -⟩ := exists_window_walks sourceArc targetArc htrav hPi hs ht
  exact (hX.reverse_map.append hB.reverse_map).isClosedDartWalk
    (fun h => hne (by simpa [invDarts] using h))

/-- **The Y-pocket walk is a closed dart walk.** -/
theorem isClosedDartWalk_Y {f : Delta.toCombMap.Face} {j : Fin Delta.rCellCount}
    (sourceArc targetArc : CyclicArc (cellDarts Delta j)) {X Y : List Delta.toCombMap.Dart}
    {r : ℕ} (htrav : (Delta.faceBoundary f).darts.rotate r =
      X ++ targetArc.reverseDarts ++ Y ++ sourceArc.reverseDarts)
    {B A : List Delta.toCombMap.Dart} {n : ℕ}
    (hPi : (cellDarts Delta j).rotate n = targetArc.darts ++ B ++ sourceArc.darts ++ A)
    (hs : 0 < sourceArc.length) (ht : 0 < targetArc.length) (hne : Y ++ A ≠ []) :
    IsClosedDartWalk Delta.toCombMap (invDarts Delta Y ++ invDarts Delta A) := by
  obtain ⟨-, -, x', y', -, -, hY, hA⟩ := exists_window_walks sourceArc targetArc htrav hPi hs ht
  exact (hY.reverse_map.append hA.reverse_map).isClosedDartWalk
    (fun h => hne (by simpa [invDarts] using h))

end Pocket

end SameCellPocketWalk

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.SameCellPocketWalk.IsWalkFromTo.append
#audit_axioms GroupApproximation.GGT.VanKampen.SameCellPocketWalk.IsWalkFromTo.reverse_map
#audit_axioms GroupApproximation.GGT.VanKampen.SameCellPocketWalk.IsWalkFromTo.exists_split
#audit_axioms GroupApproximation.GGT.VanKampen.SameCellPocketWalk.IsWalkFromTo.eq_of_ne_nil
#audit_axioms GroupApproximation.GGT.VanKampen.SameCellPocketWalk.IsWalkFromTo.isClosedDartWalk
#audit_axioms GroupApproximation.GGT.VanKampen.SameCellPocketWalk.exists_isWalkFromTo_faceBoundary_rotate
#audit_axioms GroupApproximation.GGT.VanKampen.SameCellPocketWalk.exists_window_walks
#audit_axioms GroupApproximation.GGT.VanKampen.SameCellPocketWalk.isClosedDartWalk_X
#audit_axioms GroupApproximation.GGT.VanKampen.SameCellPocketWalk.isClosedDartWalk_Y
