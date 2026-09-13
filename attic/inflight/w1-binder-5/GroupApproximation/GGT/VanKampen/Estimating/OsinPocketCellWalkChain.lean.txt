import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellWalk
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketWalkChain
import GroupApproximation.Meta.AxiomGuard

/-!
# The pocket walk of two regions joining the same two cells is a closed walk

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): two distinct selected regions joining the
same two distinct cells `Π_i` and `Π_j` bound a subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2`, where `s_1`, `s_2` are sides of the two regions and `t_1`, `t_2` are
arcs of `Π_i` and `Π_j`.

The path `s_1 t_1 s_2 t_2` is closed: each piece ends at the vertex where the next one begins, and
`t_2` ends where `s_1` begins.  For the dart list `CellPocketWalk.walk` these are the `chain` and
`closes` fields of `IsNoncrossingClosedWalk`: `vertexOf (alpha d) = vertexOf e` for consecutive
darts `d`, `e`, and for the last and the first dart.  This is the cell-to-cell analogue of
`PocketWalk.exists_of_exteriorAt_closedWalk` (`OsinPocketWalkChain`).

* `closedWalk_isChain_closes_of_interleave`: a list `s_1 t_1 s_2 t_2` is a closed walk when the
  lists `A_1 s_2 A_2` and `B_2 s_1 B_1` are walks and `t_1`, `t_2` are nonempty walks with
  `t_1` starting with `B_1` and ending with `A_1`, and `t_2` starting with `A_2` and ending with
  `B_2`.
* `CellPocketWalk.walk_isChain_closes`: let `s_1` be the side of `b` leaving `Π_j`, `t_1` an arc of
  `Π_i` spanning the arc of `a`, a gap and the arc of `b`, `s_2` the side of `a` leaving `Π_i`, and
  `t_2` an arc of `Π_j` spanning the arc of `b`, a gap and the arc of `a`.  Then the walk is closed.
  The joints `t_2 s_1` and `s_1 t_1` come from the boundary cycle of `b`, and the joints `t_1 s_2`
  and `s_2 t_2` from that of `a`.
* `CellPocketWalk.exists_of_joinsCells_closedWalk`: the walk of
  `CellPocketWalk.exists_of_joinsCells` is a nonempty closed walk.

## Manuscript status

Infrastructure for `thm:hull` ("Hull's small cancellation theorem", through Osin's
Lemma 9.7(b)); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded

section Walks

variable {α : Type*} {R : α → α → Prop}

private theorem cellWalk_getLast_head_of_closes {l : List α} (hne : l ≠ [])
    (h : ∀ a ∈ l.getLast?, ∀ b ∈ l.head?, R a b) : R (l.getLast hne) (l.head hne) :=
  h _ (Option.mem_def.mpr (List.getLast?_eq_some_getLast hne)) _
    (Option.mem_def.mpr (List.head?_eq_some_head hne))

private theorem cellWalk_getLast?_append {l₁ l₂ : List α} (h : l₂ ≠ []) :
    (l₁ ++ l₂).getLast? = l₂.getLast? := by
  rw [List.getLast?_append, List.getLast?_eq_some_getLast h, Option.some_or]

private theorem cellWalk_head?_append {l₁ l₂ : List α} (h : l₁ ≠ []) :
    (l₁ ++ l₂).head? = l₁.head? := by
  rw [List.head?_append, List.head?_eq_some_head h, Option.some_or]

/-- **Interleaving two walks gives a closed walk.**  Let `A_1 s_2 A_2` and `B_2 s_1 B_1` be walks,
and `t_1`, `t_2` nonempty walks, with `t_1` starting with the first element of `B_1` and ending
with the last element of `A_1`, and `t_2` starting with the first element of `A_2` and ending with
the last element of `B_2`.  Then `s_1 t_1 s_2 t_2` is a walk whose last and first elements are
related. -/
theorem closedWalk_isChain_closes_of_interleave {S₁ T₁ S₂ T₂ A₁ A₂ B₁ B₂ : List α}
    (hA : (A₁ ++ S₂ ++ A₂).IsChain R) (hB : (B₂ ++ S₁ ++ B₁).IsChain R)
    (hT₁ : T₁.IsChain R) (hT₂ : T₂.IsChain R) (hT₁ne : T₁ ≠ []) (hT₂ne : T₂ ≠ [])
    (hT₁h : T₁.head? = B₁.head?) (hT₁l : T₁.getLast? = A₁.getLast?)
    (hT₂h : T₂.head? = A₂.head?) (hT₂l : T₂.getLast? = B₂.getLast?) :
    (S₁ ++ T₁ ++ S₂ ++ T₂).IsChain R ∧
      ∀ a ∈ (S₁ ++ T₁ ++ S₂ ++ T₂).getLast?, ∀ b ∈ (S₁ ++ T₁ ++ S₂ ++ T₂).head?, R a b := by
  obtain ⟨t₁, ht₁⟩ : ∃ t, T₁.getLast? = some t := ⟨_, List.getLast?_eq_some_getLast hT₁ne⟩
  obtain ⟨t₂, ht₂⟩ : ∃ t, T₂.getLast? = some t := ⟨_, List.getLast?_eq_some_getLast hT₂ne⟩
  obtain ⟨h₁, h₁'⟩ : ∃ t, T₁.head? = some t := ⟨_, List.head?_eq_some_head hT₁ne⟩
  have hA₁ : A₁.getLast? = some t₁ := by
    rw [← hT₁l]
    exact ht₁
  have hAS := List.isChain_append.mp hA.left_of_append
  have hASA := List.isChain_append.mp hA
  have hBS := List.isChain_append.mp hB.left_of_append
  have hBSB := List.isChain_append.mp hB
  have hlast₁ : (S₁ ++ T₁).getLast? = some t₁ := by
    rw [List.getLast?_append, ht₁, Option.some_or]
  have hlast₂ : (S₁ ++ T₁ ++ S₂).getLast? = (A₁ ++ S₂).getLast? := by
    simp only [List.getLast?_append, ht₁, hA₁, Option.some_or]
  have J1 : ∀ x ∈ S₁.getLast?, ∀ y ∈ T₁.head?, R x y := by
    intro x hx y hy
    rw [hT₁h] at hy
    exact hBSB.2.2 x (List.mem_getLast?_append_of_mem_getLast? hx) y hy
  have J2 : ∀ x ∈ (S₁ ++ T₁).getLast?, ∀ y ∈ S₂.head?, R x y := by
    intro x hx y hy
    rw [hlast₁] at hx
    exact hAS.2.2 x (by rw [hA₁]; exact hx) y hy
  have J3 : ∀ x ∈ (S₁ ++ T₁ ++ S₂).getLast?, ∀ y ∈ T₂.head?, R x y := by
    intro x hx y hy
    rw [hlast₂] at hx
    rw [hT₂h] at hy
    exact hASA.2.2 x hx y hy
  refine ⟨List.isChain_append.mpr ⟨List.isChain_append.mpr ⟨List.isChain_append.mpr
    ⟨hBS.2.1, hT₁, J1⟩, hAS.2.1, J2⟩, hT₂, J3⟩, ?_⟩
  intro x hx y hy
  have hx' : x ∈ B₂.getLast? := by
    have h : (S₁ ++ T₁ ++ S₂ ++ T₂).getLast? = some t₂ := by
      rw [List.getLast?_append, ht₂, Option.some_or]
    rw [h] at hx
    rw [← hT₂l, ht₂]
    exact hx
  by_cases hS₁ : S₁ = []
  · subst hS₁
    have hy' : y ∈ B₁.head? := by
      have h : ([] ++ T₁ ++ S₂ ++ T₂).head? = some h₁ := by
        simp only [List.nil_append, List.head?_append, h₁', Option.some_or]
      rw [h] at hy
      rw [← hT₁h, h₁']
      exact hy
    exact hBSB.2.2 x (by rw [List.append_nil]; exact hx') y hy'
  · obtain ⟨s, hs⟩ : ∃ s, S₁.head? = some s := ⟨_, List.head?_eq_some_head hS₁⟩
    have hy' : y ∈ S₁.head? := by
      have h : (S₁ ++ T₁ ++ S₂ ++ T₂).head? = some s := by
        simp only [List.head?_append, hs, Option.some_or]
      rw [h] at hy
      rw [hs]
      exact hy
    exact hBS.2.2 x hx' y hy'

end Walks

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ}

namespace CellPocketWalk

section Diagram

variable {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- The cell pocket walk is nonempty: its arc `t_2` is. -/
theorem walk_ne_nil (K : CellPocketWalk D eps X i j) : K.walk ≠ [] := by
  have hpos := K.secondArc_pos
  rw [walk]
  refine List.append_ne_nil_of_right_ne_nil _ fun h => ?_
  have hlen := congrArg List.length h
  simp only [invDarts, List.length_map, List.length_reverse, K.secondArc.darts_length,
    List.length_nil] at hlen
  omega

/-- **The cell pocket walk `s_1 t_1 s_2 t_2` is a closed walk.**  Let `a`, `b` be regions joining the
distinct cells `i` and `j`, with nonempty arcs on both cells.  Let `s_1` be the side of `b` leaving
`Π_j`, `t_1` an arc of `Π_i` whose darts are the arc of `a`, a gap and the arc of `b`, `s_2` the
side of `a` leaving `Π_i`, and `t_2` an arc of `Π_j` whose darts are the arc of `b`, a gap and the
arc of `a`.  Then consecutive darts of the walk, and its last and first darts, meet at a vertex. -/
theorem walk_isChain_closes (K : CellPocketWalk D eps X i j) {a b : RegionCandidate D eps X}
    (hij : i ≠ j) (ha : a.JoinsCells i j) (hb : b.JoinsCells i j)
    (hai : 0 < (a.cellArcList i).length) (hbi : 0 < (b.cellArcList i).length)
    (haj : 0 < (a.cellArcList j).length) (hbj : 0 < (b.cellArcList j).length)
    (hfirst : K.firstSide = b.sideFrom j) (hsecond : K.secondSide = a.sideFrom i)
    (G₁ G₂ : List X.toCombMap.Dart)
    (h₁ : K.firstArc.darts = a.cellArcList i ++ G₁ ++ b.cellArcList i)
    (h₂ : K.secondArc.darts = b.cellArcList j ++ G₂ ++ a.cellArcList j) :
    (K.walk.IsChain fun d e =>
      X.toCombMap.vertexOf (X.toCombMap.alpha d) = X.toCombMap.vertexOf e) ∧
      ∀ x ∈ K.walk.getLast?, ∀ y ∈ K.walk.head?,
        X.toCombMap.vertexOf (X.toCombMap.alpha x) = X.toCombMap.vertexOf y := by
  -- The boundary cycle of a region joining `i` and `j`, rotated to start at `Π_i`, is a closed
  -- walk, so each of its rotations is a walk.
  have hcycle : ∀ z : RegionCandidate D eps X, z.JoinsCells i j → ∀ m : ℕ,
      ((invDarts X (z.cellArcList i) ++ z.sideFrom i ++ invDarts X (z.cellArcList j) ++
        z.sideFrom j).rotate m).IsChain fun d e =>
          X.toCombMap.vertexOf (X.toCombMap.alpha d) = X.toCombMap.vertexOf e := by
    intro z hz m
    obtain ⟨n, hn⟩ := RegionCandidate.boundary_cycle_rotate_of_joinsCells hij hz
    obtain ⟨hchain, hcloses⟩ := z.2.boundary.isChain_closes
    have hne : z.2.boundary.cycle ≠ [] := z.2.boundary.cycle_nonempty
    rw [← hn, List.rotate_rotate]
    exact isChain_rotate_of_isChain_closes hne hchain
      (cellWalk_getLast_head_of_closes hne hcloses) (n + m)
  have hA : (invDarts X (a.cellArcList i) ++ a.sideFrom i ++
      invDarts X (a.cellArcList j)).IsChain fun d e =>
        X.toCombMap.vertexOf (X.toCombMap.alpha d) = X.toCombMap.vertexOf e := by
    have h := hcycle a ha 0
    rw [List.rotate_zero] at h
    exact h.left_of_append
  have hB : (invDarts X (b.cellArcList j) ++ b.sideFrom j ++
      invDarts X (b.cellArcList i)).IsChain fun d e =>
        X.toCombMap.vertexOf (X.toCombMap.alpha d) = X.toCombMap.vertexOf e := by
    have h := hcycle b hb (invDarts X (b.cellArcList i) ++ b.sideFrom i).length
    rw [List.append_assoc (invDarts X (b.cellArcList i) ++ b.sideFrom i),
      List.rotate_append_length_eq, ← List.append_assoc] at h
    exact h.left_of_append
  -- The arcs `t_1` and `t_2`, read backwards, are walks with the right ends.
  obtain ⟨hcelli, hcellic⟩ := isChain_closes_cellDarts X i
  obtain ⟨hcellj, hcelljc⟩ := isChain_closes_cellDarts X j
  have hT₁ := isChain_invDarts (Delta := X) (K.firstArc.isChain_darts hcelli hcellic)
  have hT₂ := isChain_invDarts (Delta := X) (K.secondArc.isChain_darts hcellj hcelljc)
  have hA₁ne : a.cellArcList i ≠ [] := List.ne_nil_of_length_pos hai
  have hB₁ne : b.cellArcList i ≠ [] := List.ne_nil_of_length_pos hbi
  have hA₂ne : a.cellArcList j ≠ [] := List.ne_nil_of_length_pos haj
  have hB₂ne : b.cellArcList j ≠ [] := List.ne_nil_of_length_pos hbj
  have hT₁ne : invDarts X K.firstArc.darts ≠ [] := by
    intro h
    have hlen := congrArg List.length h
    simp only [invDarts, List.length_map, List.length_reverse, K.firstArc.darts_length,
      List.length_nil] at hlen
    have hpos := K.firstArc_pos
    omega
  have hT₂ne : invDarts X K.secondArc.darts ≠ [] := by
    intro h
    have hlen := congrArg List.length h
    simp only [invDarts, List.length_map, List.length_reverse, K.secondArc.darts_length,
      List.length_nil] at hlen
    have hpos := K.secondArc_pos
    omega
  have hT₁h : (invDarts X K.firstArc.darts).head? = (invDarts X (b.cellArcList i)).head? := by
    rw [head?_invDarts, head?_invDarts, h₁, cellWalk_getLast?_append hB₁ne]
  have hT₁l : (invDarts X K.firstArc.darts).getLast? =
      (invDarts X (a.cellArcList i)).getLast? := by
    rw [getLast?_invDarts, getLast?_invDarts, h₁,
      cellWalk_head?_append (List.append_ne_nil_of_left_ne_nil hA₁ne _),
      cellWalk_head?_append hA₁ne]
  have hT₂h : (invDarts X K.secondArc.darts).head? = (invDarts X (a.cellArcList j)).head? := by
    rw [head?_invDarts, head?_invDarts, h₂, cellWalk_getLast?_append hA₂ne]
  have hT₂l : (invDarts X K.secondArc.darts).getLast? =
      (invDarts X (b.cellArcList j)).getLast? := by
    rw [getLast?_invDarts, getLast?_invDarts, h₂,
      cellWalk_head?_append (List.append_ne_nil_of_left_ne_nil hB₂ne _),
      cellWalk_head?_append hB₂ne]
  have hwalk : K.walk = b.sideFrom j ++ invDarts X K.firstArc.darts ++ a.sideFrom i ++
      invDarts X K.secondArc.darts := by
    rw [walk, hfirst, hsecond]
  rw [hwalk]
  exact closedWalk_isChain_closes_of_interleave hA hB hT₁ hT₂ hT₁ne hT₂ne hT₁h hT₁l hT₂h hT₂l

end Diagram

variable {Delta : DiscDiagram.{u, w, v} W} {lambda c : ℝ}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}

/-- **The pocket walk of two regions joining the same two cells is a nonempty closed walk.**  The
walk of `exists_of_joinsCells`, with the same data, is nonempty, and consecutive darts, and the
last and the first dart, meet at a vertex. -/
theorem exists_of_joinsCells_closedWalk (S : RealizedSectionFamily D lambda c eps Delta cuts)
    {i j : Fin S.diagram.rCellCount} {a b : RegionCandidate D eps S.diagram}
    (ha : a ∈ S.family) (hb : b ∈ S.family) (hab : a ≠ b) (hij : i ≠ j)
    (hai : a.JoinsCells i j) (hbi : b.JoinsCells i j) :
    ∃ K : CellPocketWalk D eps S.diagram i j,
      K.firstSide = b.sideFrom j ∧ K.secondSide = a.sideFrom i ∧
        (∃ G₁ : CyclicArc (cellDarts S.diagram i),
          K.firstArc.darts = a.cellArcList i ++ G₁.darts ++ b.cellArcList i) ∧
        (∃ G₂ : CyclicArc (cellDarts S.diagram j),
          K.secondArc.darts = b.cellArcList j ++ G₂.darts ++ a.cellArcList j) ∧
        ∃ hne : K.walk ≠ [],
          (K.walk.IsChain fun d e => S.diagram.toCombMap.vertexOf
            (S.diagram.toCombMap.alpha d) = S.diagram.toCombMap.vertexOf e) ∧
          S.diagram.toCombMap.vertexOf (S.diagram.toCombMap.alpha (K.walk.getLast hne)) =
            S.diagram.toCombMap.vertexOf (K.walk.head hne) := by
  obtain ⟨K, hfirst, hsecond, ⟨G₁, h₁⟩, ⟨G₂, h₂⟩⟩ := exists_of_joinsCells S ha hb hab hai hbi
  have hna := RegionCandidate.cellArcList_length_pos (S.nondegenerate a ha)
  have hnb := RegionCandidate.cellArcList_length_pos (S.nondegenerate b hb)
  obtain ⟨hchain, hcloses⟩ := K.walk_isChain_closes hij hai hbi (hna i) (hnb i) (hna j) (hnb j)
    hfirst hsecond G₁.darts G₂.darts h₁ h₂
  exact ⟨K, hfirst, hsecond, ⟨G₁, h₁⟩, ⟨G₂, h₂⟩, K.walk_ne_nil, hchain,
    cellWalk_getLast_head_of_closes K.walk_ne_nil hcloses⟩

end CellPocketWalk

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.closedWalk_isChain_closes_of_interleave
#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketWalk.walk_ne_nil
#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketWalk.walk_isChain_closes
#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketWalk.exists_of_joinsCells_closedWalk
