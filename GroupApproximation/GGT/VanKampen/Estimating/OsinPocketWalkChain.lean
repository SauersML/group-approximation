import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketSectionFaceSet
import GroupApproximation.GGT.VanKampen.FaceSetBoundaryRotation
import GroupApproximation.Meta.AxiomGuard

/-!
# The pocket walk of two exterior regions is a closed walk

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b):

> "Let us consider the subdiagram `Γ_1` of `Δ` such that: (i) `∂Γ_1 = s_1 t_1 s_2 t_2`, where
> `s_1, s_2` are side arcs of some of `Γ_{i,1}`'s and `t_1, t_2` are subpaths of `∂Π` and the
> section `q_1` of `∂Δ`, respectively; (ii) `Γ_1` contains all `Γ_{i,1}`'s."

A path `s_1 t_1 s_2 t_2` is closed: each piece ends at the vertex where the next one begins, and
`t_2` ends where `s_1` begins.  For a dart list `w` this is the `chain` and `closes` data of a
closed walk: `vertexOf (alpha d) = vertexOf e` for consecutive darts `d`, `e`, and for the last and
the first dart.

* A face boundary is a closed walk (`vertexOf_alpha_eq_of_facePerm`), and so is the boundary cycle
  of a face set (`FaceSetBoundary.isChain_closes`): crossing an internal edge keeps the vertex.
* A closed walk read backwards is a closed walk (`isChain_invDarts`, `closes_invDarts`), and the
  darts of an arc of a closed walk form a walk (`CyclicArc.isChain_darts`).
* Two nonempty arcs of one carrier with a common start have a common first dart
  (`CyclicArc.head?_darts_eq`); with a common end inside the carrier they have a common last dart
  (`CyclicArc.getLast?_darts_eq`).
* `PocketWalk.walk_isChain_closes`: let `x`, `y` be regions to the outer boundary, `s_1` the left
  side of `y`, `t_1` an arc of the source cell spanning the source arcs of `x` and `y`, `s_2` the
  right side of `x`, and `t_2` the outer arc from the start of `x`'s target arc to the end of `y`'s.
  Then `s_1 t_1 s_2 t_2` is a closed walk.  The joints `s_1 t_1` and `t_2 s_1` come from the
  boundary cycle of `y`, the joints `t_1 s_2` and `s_2 t_2` from the boundary cycle of `x`.
* `PocketWalk.exists_of_exteriorAt_closedWalk`: the pocket walk of two exterior regions of a
  realized section family is a nonempty closed walk.

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, "Hull's small cancellation theorem", through Osin's
Lemma 9.7(b)); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded

section Walks

variable {α : Type*} {R : α → α → Prop}

private theorem head?_append_of_left_ne_nil {l₁ l₂ : List α} (h : l₁ ≠ []) :
    (l₁ ++ l₂).head? = l₁.head? := by
  rw [List.head?_append, List.head?_eq_some_head h, Option.some_or]

private theorem getLast?_append_of_right_ne_nil {l₁ l₂ : List α} (h : l₂ ≠ []) :
    (l₁ ++ l₂).getLast? = l₂.getLast? := by
  rw [List.getLast?_append, List.getLast?_eq_some_getLast h, Option.some_or]

private theorem closes_of_getLast_head {l : List α} (hne : l ≠ [])
    (h : R (l.getLast hne) (l.head hne)) : ∀ a ∈ l.getLast?, ∀ b ∈ l.head?, R a b := by
  intro a ha b hb
  obtain rfl := Option.some.inj
    ((List.getLast?_eq_some_getLast hne).symm.trans (Option.mem_def.mp ha))
  obtain rfl := Option.some.inj
    ((List.head?_eq_some_head hne).symm.trans (Option.mem_def.mp hb))
  exact h

private theorem getLast_head_of_closes {l : List α} (hne : l ≠ [])
    (h : ∀ a ∈ l.getLast?, ∀ b ∈ l.head?, R a b) : R (l.getLast hne) (l.head hne) :=
  h _ (Option.mem_def.mpr (List.getLast?_eq_some_getLast hne)) _
    (Option.mem_def.mpr (List.head?_eq_some_head hne))

end Walks

namespace Embedded.CyclicArc

variable {Dart : Type v} {cycle : List Dart}

/-- **An arc of a closed walk is a walk.** -/
theorem isChain_darts {R : Dart → Dart → Prop} (arc : CyclicArc cycle)
    (hchain : cycle.IsChain R) (hcloses : ∀ a ∈ cycle.getLast?, ∀ b ∈ cycle.head?, R a b) :
    arc.darts.IsChain R := by
  rw [darts, arc.rotated_eq_rotate]
  by_cases hne : cycle = []
  · subst hne
    rw [List.rotate_nil, List.take_nil]
    exact List.isChain_nil
  · exact (isChain_rotate_of_isChain_closes hne hchain (getLast_head_of_closes hne hcloses)
      _).take _

/-- **Arcs with a common start have a common first dart.** -/
theorem head?_darts_eq (arc₁ arc₂ : CyclicArc cycle) (h₁ : 0 < arc₁.length)
    (h₂ : 0 < arc₂.length) (hs : arc₁.start.1 = arc₂.start.1) :
    arc₁.darts.head? = arc₂.darts.head? := by
  have h₁' : arc₁.length ≠ 0 := by omega
  have h₂' : arc₂.length ≠ 0 := by omega
  rw [darts, darts, List.head?_take, List.head?_take, if_neg h₁', if_neg h₂', rotated, rotated,
    hs]

/-- The last dart of a nonempty arc ending inside its carrier. -/
theorem getLast?_darts_of_add_le (arc : CyclicArc cycle) (hpos : 0 < arc.length)
    (h : arc.start.1 + arc.length ≤ cycle.length) :
    arc.darts.getLast? = cycle[arc.start.1 + arc.length - 1]? := by
  have hlen : arc.length ≤ (cycle.drop arc.start.1).length := by
    rw [List.length_drop]
    omega
  have htake : ((cycle.drop arc.start.1).take arc.length).length = arc.length := by
    rw [List.length_take]
    omega
  have hlt : arc.length - 1 < arc.length := by omega
  rw [darts, rotated, List.take_append_of_le_length hlen, List.getLast?_eq_getElem?, htake,
    List.getElem?_take, if_pos hlt, List.getElem?_drop,
    show arc.start.1 + (arc.length - 1) = arc.start.1 + arc.length - 1 by omega]

/-- **Arcs with a common end inside the carrier have a common last dart.** -/
theorem getLast?_darts_eq (arc₁ arc₂ : CyclicArc cycle) (h₁ : 0 < arc₁.length)
    (h₂ : 0 < arc₂.length)
    (hend : arc₁.start.1 + arc₁.length = arc₂.start.1 + arc₂.length)
    (hle : arc₂.start.1 + arc₂.length ≤ cycle.length) :
    arc₁.darts.getLast? = arc₂.darts.getLast? := by
  rw [getLast?_darts_of_add_le arc₁ h₁ (by omega), getLast?_darts_of_add_le arc₂ h₂ hle,
    hend]

end Embedded.CyclicArc

namespace Embedded

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- **A face step keeps the vertex.**  If the face rotation takes `d` to `e`, then `e` starts at
the vertex where `d` ends. -/
theorem vertexOf_alpha_eq_of_facePerm {M : CombMap} {d e : M.Dart} (h : M.facePerm d = e) :
    M.vertexOf (M.alpha d) = M.vertexOf e := by
  subst h
  exact (M.vertexOf_sigma (M.alpha d)).symm

/-- **A boundary step keeps the vertex.**  Advancing once around a face, then crossing internal
edges each followed by a face step, gives a dart starting at the vertex where the first dart
ends. -/
theorem vertexOf_alpha_eq_of_boundaryStep {Delta : DiscDiagram.{u, w, v} W}
    {faces : Finset Delta.toCombMap.Face} {d e : Delta.toCombMap.Dart}
    (h : BoundaryStep Delta faces d e) :
    Delta.toCombMap.vertexOf (Delta.toCombMap.alpha d) = Delta.toCombMap.vertexOf e := by
  obtain ⟨-, -, h⟩ := h
  induction h with
  | refl => exact (Delta.toCombMap.vertexOf_sigma (Delta.toCombMap.alpha d)).symm
  | @tail b _ _ hmove ih =>
    obtain ⟨-, -, rfl⟩ := hmove
    rw [ih]
    show Delta.toCombMap.vertexOf b = Delta.toCombMap.vertexOf
      (Delta.toCombMap.sigma (Delta.toCombMap.alpha (Delta.toCombMap.alpha b)))
    rw [Delta.toCombMap.vertexOf_sigma, Delta.toCombMap.alpha_involutive b]

/-- **A face boundary is a closed walk.** -/
theorem isChain_closes_of_faceBoundary {M : CombMap} {f : M.Face} (B : FaceBoundary M f) :
    (B.darts.IsChain fun d e => M.vertexOf (M.alpha d) = M.vertexOf e) ∧
      ∀ a ∈ B.darts.getLast?, ∀ b ∈ B.darts.head?, M.vertexOf (M.alpha a) = M.vertexOf b :=
  ⟨B.chain.imp fun _ _ h => vertexOf_alpha_eq_of_facePerm h,
    closes_of_getLast_head B.nonempty (vertexOf_alpha_eq_of_facePerm B.closes)⟩

/-- **The boundary cycle of a face set is a closed walk.** -/
theorem FaceSetBoundary.isChain_closes {Delta : DiscDiagram.{u, w, v} W}
    {faces : Finset Delta.toCombMap.Face} (B : FaceSetBoundary Delta faces) :
    (B.cycle.IsChain fun d e =>
      Delta.toCombMap.vertexOf (Delta.toCombMap.alpha d) = Delta.toCombMap.vertexOf e) ∧
      ∀ a ∈ B.cycle.getLast?, ∀ b ∈ B.cycle.head?,
        Delta.toCombMap.vertexOf (Delta.toCombMap.alpha a) = Delta.toCombMap.vertexOf b :=
  ⟨B.cycle_chain.imp fun _ _ h => vertexOf_alpha_eq_of_boundaryStep h,
    closes_of_getLast_head B.cycle_nonempty (vertexOf_alpha_eq_of_boundaryStep B.cycle_closes)⟩

/-- The first dart of a dart list read backwards is the reverse of its last dart. -/
theorem head?_invDarts (Delta : DiscDiagram.{u, w, v} W) (l : List Delta.toCombMap.Dart) :
    (invDarts Delta l).head? = l.getLast?.map Delta.toCombMap.alpha := by
  rw [invDarts, List.head?_map, List.head?_reverse]

/-- The last dart of a dart list read backwards is the reverse of its first dart. -/
theorem getLast?_invDarts (Delta : DiscDiagram.{u, w, v} W) (l : List Delta.toCombMap.Dart) :
    (invDarts Delta l).getLast? = l.head?.map Delta.toCombMap.alpha := by
  rw [invDarts, List.getLast?_map, List.getLast?_reverse]

/-- **A walk read backwards is a walk.** -/
theorem isChain_invDarts {Delta : DiscDiagram.{u, w, v} W} {l : List Delta.toCombMap.Dart}
    (h : l.IsChain fun d e =>
      Delta.toCombMap.vertexOf (Delta.toCombMap.alpha d) = Delta.toCombMap.vertexOf e) :
    (invDarts Delta l).IsChain fun d e =>
      Delta.toCombMap.vertexOf (Delta.toCombMap.alpha d) = Delta.toCombMap.vertexOf e := by
  rw [invDarts, List.isChain_map, List.isChain_reverse]
  refine h.imp fun a b hab => ?_
  show Delta.toCombMap.vertexOf (Delta.toCombMap.alpha (Delta.toCombMap.alpha b)) =
    Delta.toCombMap.vertexOf (Delta.toCombMap.alpha a)
  rw [Delta.toCombMap.alpha_involutive b]
  exact Eq.symm hab

/-- **A closed walk read backwards is closed.** -/
theorem closes_invDarts {Delta : DiscDiagram.{u, w, v} W} {l : List Delta.toCombMap.Dart}
    (h : ∀ a ∈ l.getLast?, ∀ b ∈ l.head?,
      Delta.toCombMap.vertexOf (Delta.toCombMap.alpha a) = Delta.toCombMap.vertexOf b) :
    ∀ a ∈ (invDarts Delta l).getLast?, ∀ b ∈ (invDarts Delta l).head?,
      Delta.toCombMap.vertexOf (Delta.toCombMap.alpha a) = Delta.toCombMap.vertexOf b := by
  intro a ha b hb
  rw [getLast?_invDarts, Option.mem_def, Option.map_eq_some_iff] at ha
  rw [head?_invDarts, Option.mem_def, Option.map_eq_some_iff] at hb
  obtain ⟨a', ha', rfl⟩ := ha
  obtain ⟨b', hb', rfl⟩ := hb
  rw [Delta.toCombMap.alpha_involutive a']
  exact Eq.symm (h b' (Option.mem_def.mpr hb') a' (Option.mem_def.mpr ha'))

/-- **The boundary of a relator cell is a closed walk.** -/
theorem isChain_closes_cellDarts (Delta : DiscDiagram.{u, w, v} W) (i : Fin Delta.rCellCount) :
    ((cellDarts Delta i).IsChain fun d e =>
      Delta.toCombMap.vertexOf (Delta.toCombMap.alpha d) = Delta.toCombMap.vertexOf e) ∧
      ∀ a ∈ (cellDarts Delta i).getLast?, ∀ b ∈ (cellDarts Delta i).head?,
        Delta.toCombMap.vertexOf (Delta.toCombMap.alpha a) = Delta.toCombMap.vertexOf b :=
  isChain_closes_of_faceBoundary (Delta.faceBoundary (cell Delta i).face)

/-- **The oriented outer boundary is a closed walk.** -/
theorem isChain_closes_outerDarts (Delta : DiscDiagram.{u, w, v} W) :
    ((outerDarts Delta).IsChain fun d e =>
      Delta.toCombMap.vertexOf (Delta.toCombMap.alpha d) = Delta.toCombMap.vertexOf e) ∧
      ∀ a ∈ (outerDarts Delta).getLast?, ∀ b ∈ (outerDarts Delta).head?,
        Delta.toCombMap.vertexOf (Delta.toCombMap.alpha a) = Delta.toCombMap.vertexOf b := by
  obtain ⟨hchain, hcloses⟩ :=
    isChain_closes_of_faceBoundary (Delta.faceBoundary Delta.outerFace)
  exact ⟨isChain_invDarts (Delta := Delta) hchain, closes_invDarts (Delta := Delta) hcloses⟩

private theorem targetBoundaryDarts_none_eq (Delta : DiscDiagram.{u, w, v} W)
    {target : Option (Fin Delta.rCellCount)} (ht : target = none)
    (arc : CyclicArc (targetDarts Delta target)) :
    targetBoundaryDarts Delta target arc = arc.darts := by
  subst ht
  rfl

end Embedded

namespace PocketWalk

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ}

section Diagram

variable {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- The pocket walk is nonempty: its outer arc `t_2` is. -/
theorem walk_ne_nil (K : PocketWalk D eps X lo hi) : K.walk ≠ [] := by
  have hpos := K.targetArc_pos
  rw [walk]
  refine List.append_ne_nil_of_right_ne_nil _ fun h => ?_
  have hlen := congrArg List.length h
  rw [K.targetArc.darts_length, List.length_nil] at hlen
  omega

/-- **The pocket walk `s_1 t_1 s_2 t_2` is a closed walk.**  Let `x`, `y` be nondegenerate regions
to the outer boundary, `s_1` the left side of `y`, `t_1` an arc of the source cell whose darts are
the source arc of `x`, a gap and the source arc of `y`, `s_2` the right side of `x`, and `t_2` an
outer arc starting with `x`'s target arc and ending, inside the outer boundary, with `y`'s.  Then
consecutive darts of the walk, and its last and first darts, meet at a vertex. -/
theorem walk_isChain_closes (K : PocketWalk D eps X lo hi) (x y : RegionCandidate D eps X)
    (hxt : x.2.target = none) (hyt : y.2.target = none)
    (hxs : 0 < x.2.sourceArc.length) (hys : 0 < y.2.sourceArc.length)
    (hxtgt : 0 < x.2.targetArc.length) (hytgt : 0 < y.2.targetArc.length)
    (hfirst : K.firstSide = y.2.leftSide) (hsecond : K.secondSide = x.2.rightSide)
    (Gap : List X.toCombMap.Dart)
    (hsrc : K.sourceArc.darts = x.2.sourceArc.darts ++ Gap ++ y.2.sourceArc.darts)
    (hstart : K.targetArc.start.1 = x.2.targetArc.start.1)
    (hend : K.targetArc.start.1 + K.targetArc.length =
      y.2.targetArc.start.1 + y.2.targetArc.length)
    (hyend : y.2.targetArc.start.1 + y.2.targetArc.length ≤ (outerDarts X).length) :
    (K.walk.IsChain fun d e =>
      X.toCombMap.vertexOf (X.toCombMap.alpha d) = X.toCombMap.vertexOf e) ∧
      ∀ a ∈ K.walk.getLast?, ∀ b ∈ K.walk.head?,
        X.toCombMap.vertexOf (X.toCombMap.alpha a) = X.toCombMap.vertexOf b := by
  obtain ⟨hCx, -⟩ := x.2.boundary.isChain_closes
  obtain ⟨hCy, hCyc⟩ := y.2.boundary.isChain_closes
  rw [x.2.boundary_decomposition, targetBoundaryDarts_none_eq X hxt] at hCx
  rw [y.2.boundary_decomposition, targetBoundaryDarts_none_eq X hyt] at hCy hCyc
  obtain ⟨hcell, hcellc⟩ := isChain_closes_cellDarts X K.source
  obtain ⟨hout, houtc⟩ := isChain_closes_outerDarts X
  have hinv := isChain_invDarts (Delta := X) (K.sourceArc.isChain_darts hcell hcellc)
  have ht₂ := K.targetArc.isChain_darts hout houtc
  have hxne : x.2.sourceArc.darts ≠ [] :=
    List.ne_nil_of_length_pos (by rw [x.2.sourceArc.darts_length]; exact hxs)
  have hyne : y.2.sourceArc.darts ≠ [] :=
    List.ne_nil_of_length_pos (by rw [y.2.sourceArc.darts_length]; exact hys)
  have hKtne : K.targetArc.darts ≠ [] :=
    List.ne_nil_of_length_pos (by rw [K.targetArc.darts_length]; exact K.targetArc_pos)
  have hinvne : invDarts X K.sourceArc.darts ≠ [] := by
    rw [hsrc]
    intro h
    have hlen := congrArg List.length h
    simp only [invDarts, List.length_map, List.length_reverse, List.length_append,
      x.2.sourceArc.darts_length, List.length_nil] at hlen
    omega
  have hinvhead : (invDarts X K.sourceArc.darts).head? =
      (invDarts X y.2.sourceArc.darts).head? := by
    rw [head?_invDarts, head?_invDarts, hsrc, getLast?_append_of_right_ne_nil hyne]
  have hinvlast : (invDarts X K.sourceArc.darts).getLast? =
      (invDarts X x.2.sourceArc.darts).getLast? := by
    rw [getLast?_invDarts, getLast?_invDarts, hsrc,
      head?_append_of_left_ne_nil (List.append_ne_nil_of_left_ne_nil hxne _),
      head?_append_of_left_ne_nil hxne]
  obtain ⟨xt, hxts, hxtl, hxtd⟩ : ∃ arc : CyclicArc (outerDarts X),
      arc.start.1 = x.2.targetArc.start.1 ∧ arc.length = x.2.targetArc.length ∧
        arc.darts = x.2.targetArc.darts :=
    CyclicArc.exists_transport (targetDarts X) hxt x.2.targetArc
  obtain ⟨yt, hyts, hytl, hytd⟩ : ∃ arc : CyclicArc (outerDarts X),
      arc.start.1 = y.2.targetArc.start.1 ∧ arc.length = y.2.targetArc.length ∧
        arc.darts = y.2.targetArc.darts :=
    CyclicArc.exists_transport (targetDarts X) hyt y.2.targetArc
  have hKthead : K.targetArc.darts.head? = x.2.targetArc.darts.head? := by
    rw [← hxtd]
    exact CyclicArc.head?_darts_eq K.targetArc xt K.targetArc_pos (by omega) (by omega)
  have hKtlast : K.targetArc.darts.getLast? = y.2.targetArc.darts.getLast? := by
    rw [← hytd]
    exact CyclicArc.getLast?_darts_eq K.targetArc yt K.targetArc_pos (by omega) (by omega)
      (by omega)
  have J1 : ∀ a ∈ y.2.leftSide.getLast?, ∀ b ∈ (invDarts X K.sourceArc.darts).head?,
      X.toCombMap.vertexOf (X.toCombMap.alpha a) = X.toCombMap.vertexOf b := by
    intro a ha b hb
    rw [hinvhead] at hb
    exact hCyc a (List.mem_getLast?_append_of_mem_getLast? ha) b
      (List.mem_head?_append_of_mem_head? (List.mem_head?_append_of_mem_head?
        (List.mem_head?_append_of_mem_head? hb)))
  have J3 : ∀ a ∈ (y.2.leftSide ++ invDarts X K.sourceArc.darts).getLast?,
      ∀ b ∈ x.2.rightSide.head?,
        X.toCombMap.vertexOf (X.toCombMap.alpha a) = X.toCombMap.vertexOf b := by
    intro a ha b hb
    rw [getLast?_append_of_right_ne_nil hinvne, hinvlast] at ha
    exact (List.isChain_append.mp hCx.left_of_append.left_of_append).2.2 a ha b hb
  have hlast : (y.2.leftSide ++ invDarts X K.sourceArc.darts ++ x.2.rightSide).getLast? =
      (invDarts X x.2.sourceArc.darts ++ x.2.rightSide).getLast? := by
    rw [List.getLast?_append, List.getLast?_append (l := invDarts X x.2.sourceArc.darts),
      getLast?_append_of_right_ne_nil hinvne, hinvlast]
  have J4 : ∀ a ∈ (y.2.leftSide ++ invDarts X K.sourceArc.darts ++ x.2.rightSide).getLast?,
      ∀ b ∈ K.targetArc.darts.head?,
        X.toCombMap.vertexOf (X.toCombMap.alpha a) = X.toCombMap.vertexOf b := by
    intro a ha b hb
    rw [hlast] at ha
    rw [hKthead] at hb
    exact (List.isChain_append.mp hCx.left_of_append).2.2 a ha b hb
  have hwalk : K.walk =
      y.2.leftSide ++ invDarts X K.sourceArc.darts ++ x.2.rightSide ++ K.targetArc.darts := by
    rw [walk, hfirst, hsecond]
  rw [hwalk]
  refine ⟨List.isChain_append.mpr ⟨List.isChain_append.mpr ⟨List.isChain_append.mpr
    ⟨hCy.right_of_append, hinv, J1⟩, hCx.left_of_append.left_of_append.right_of_append, J3⟩,
    ht₂, J4⟩, ?_⟩
  intro a ha b hb
  rw [getLast?_append_of_right_ne_nil hKtne, hKtlast] at ha
  by_cases hyl : y.2.leftSide = []
  · rw [hyl, List.nil_append,
      head?_append_of_left_ne_nil (List.append_ne_nil_of_left_ne_nil hinvne _),
      head?_append_of_left_ne_nil hinvne, hinvhead] at hb
    rw [hyl, List.append_nil] at hCyc
    exact hCyc a (List.mem_getLast?_append_of_mem_getLast? ha) b
      (List.mem_head?_append_of_mem_head? (List.mem_head?_append_of_mem_head? hb))
  · rw [head?_append_of_left_ne_nil
        (List.append_ne_nil_of_left_ne_nil (List.append_ne_nil_of_left_ne_nil hyl _) _),
      head?_append_of_left_ne_nil (List.append_ne_nil_of_left_ne_nil hyl _),
      head?_append_of_left_ne_nil hyl] at hb
    exact (List.isChain_append.mp hCy).2.2 a (List.mem_getLast?_append_of_mem_getLast? ha) b hb

end Diagram

variable {Delta : DiscDiagram.{u, w, v} W} {lambda c : ℝ}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}

/-- **The pocket walk of two exterior regions is a nonempty closed walk.**  The pocket walk of
`exists_of_exteriorAt`, with the same data, is nonempty, and consecutive darts, and the last and
the first dart, meet at a vertex. -/
theorem exists_of_exteriorAt_closedWalk (S : RealizedSectionFamily D lambda c eps Delta cuts)
    {i : Fin S.diagram.rCellCount} {j : Fin cuts.count} {a b : RegionCandidate D eps S.diagram}
    (ha : a ∈ RegionCandidate.exteriorAt S.family i)
    (hb : b ∈ RegionCandidate.exteriorAt S.family i) (hab : a ≠ b)
    (hja : RegionCandidate.TargetsSectionIndex cuts j a)
    (hjb : RegionCandidate.TargetsSectionIndex cuts j b) :
    ∃ (K : PocketWalk D eps S.diagram (cuts.cut j.castSucc) (cuts.cut j.succ))
      (x y : RegionCandidate D eps S.diagram), (x = a ∧ y = b ∨ x = b ∧ y = a) ∧
      K.source = i ∧ K.firstSide = y.2.leftSide ∧ K.secondSide = x.2.rightSide ∧
        (∃ Gap : CyclicArc (cellDarts S.diagram i),
          K.sourceArc.darts = x.2.sourceArc.darts ++ Gap.darts ++ y.2.sourceArc.darts) ∧
        K.targetArc.start.1 = x.2.targetArc.start.1 ∧
        K.targetArc.start.1 + K.targetArc.length =
          y.2.targetArc.start.1 + y.2.targetArc.length ∧
        ∃ hne : K.walk ≠ [],
          (K.walk.IsChain fun d e => S.diagram.toCombMap.vertexOf
            (S.diagram.toCombMap.alpha d) = S.diagram.toCombMap.vertexOf e) ∧
          S.diagram.toCombMap.vertexOf (S.diagram.toCombMap.alpha (K.walk.getLast hne)) =
            S.diagram.toCombMap.vertexOf (K.walk.head hne) := by
  obtain ⟨K, x, y, hxy, hKi, hfirst, hsecond, ⟨Gap, hsrc⟩, hstart, hend⟩ :=
    exists_of_exteriorAt S ha hb hab hja hjb
  have hmem : ∀ z ∈ RegionCandidate.exteriorAt S.family i, z ∈ S.family := fun z hz =>
    (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).1
  obtain ⟨hxS, hjx, hyS, hjy⟩ :
      x ∈ S.family ∧ RegionCandidate.TargetsSectionIndex cuts j x ∧
        y ∈ S.family ∧ RegionCandidate.TargetsSectionIndex cuts j y := by
    rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨hmem _ ha, hja, hmem _ hb, hjb⟩
    · exact ⟨hmem _ hb, hjb, hmem _ ha, hja⟩
  obtain ⟨hxs, hxtgt⟩ := S.nondegenerate x hxS
  obtain ⟨hys, hytgt⟩ := S.nondegenerate y hyS
  obtain ⟨hxt, -, -⟩ := hjx
  obtain ⟨hyt, -, hyhi⟩ := hjy
  have hyend : y.2.targetArc.start.1 + y.2.targetArc.length ≤ (outerDarts S.diagram).length :=
    Nat.le_trans hyhi (cut_le_length_outerDarts S j.succ)
  obtain ⟨hchain, hcloses⟩ := walk_isChain_closes K x y hxt hyt hxs hys hxtgt hytgt hfirst
    hsecond Gap.darts hsrc hstart hend hyend
  exact ⟨K, x, y, hxy, hKi, hfirst, hsecond, ⟨Gap, hsrc⟩, hstart, hend, K.walk_ne_nil, hchain,
    getLast_head_of_closes K.walk_ne_nil hcloses⟩

end PocketWalk

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.CyclicArc.isChain_darts
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.CyclicArc.head?_darts_eq
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.CyclicArc.getLast?_darts_of_add_le
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.CyclicArc.getLast?_darts_eq
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.vertexOf_alpha_eq_of_facePerm
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.vertexOf_alpha_eq_of_boundaryStep
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.isChain_closes_of_faceBoundary
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.FaceSetBoundary.isChain_closes
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.head?_invDarts
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.getLast?_invDarts
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.isChain_invDarts
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.closes_invDarts
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.isChain_closes_cellDarts
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.isChain_closes_outerDarts
#audit_axioms GroupApproximation.GGT.VanKampen.PocketWalk.walk_ne_nil
#audit_axioms GroupApproximation.GGT.VanKampen.PocketWalk.walk_isChain_closes
#audit_axioms GroupApproximation.GGT.VanKampen.PocketWalk.exists_of_exteriorAt_closedWalk
