import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94SameCellPocketWalk
import GroupApproximation.Meta.AxiomGuard

/-!
# GL06p: a nearest relator cell and a minimal path to it

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b), the all-cells case: "let `Π` be a cell of
`Δ` nearest to `∂Δ`, and `p` a path of minimal length from `∂Δ` to `∂Π`".  Infrastructure for
`thm:hull` (non_mf_groups_exist.tex ~2121, Hull's small cancellation theorem, through Osin's
Lemma 9.7).  Step 1 of lane nm-gl06e's construction of the slit pocket
`GL06h4.gl06h4Nearest_Pocket`.

* `WalkReach`, `walkReach_of_eqvGen`: in a connected combinatorial map the base vertices of any
  two darts are joined by a walk (`SameCellPocketWalk.IsWalkFromTo`).
* `IsBoundaryToCellWalk`: a walk from a vertex of the outer face to a vertex of a relator cell.
* `exists_boundaryToCellWalk`: every relator cell of a disc diagram is reached from the boundary,
  since a disc diagram is planar, so connected.
* `NearestCellPath`, `exists_nearestCellPath`: a cell and a walk to it of minimal length among
  all walks from the boundary to all relator cells, whenever the diagram has a relator cell.

## Manuscript status

Infrastructure for `thm:hull` (non_mf_groups_exist.tex ~2121); certifies no printed sentence on
its own.  No hypothesis is added.
-/

namespace GroupApproximation.Full.GL06p

universe u w v

open GroupApproximation.GGT
open GroupApproximation.GGT.VanKampen
open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.GGT.VanKampen.SameCellPocketWalk

section Reach

variable (M : CombMap.{v})

/-- **Two darts' base vertices are joined by a walk.** -/
def WalkReach (d e : M.Dart) : Prop :=
  ∃ l : List M.Dart, IsWalkFromTo M l (M.vertexOf d) (M.vertexOf e)

/-- An elementary dart move is joined by a walk: an edge reversal by the one-dart walk, a vertex
rotation by the empty walk. -/
theorem walkReach_of_adjacent {d e : M.Dart} (h : M.Adjacent d e) : WalkReach M d e := by
  rcases h with h | h
  · subst h
    refine ⟨[d], List.isChain_singleton d, fun a ha => ?_, fun a ha => ?_,
      fun hnil => (List.cons_ne_nil d [] hnil).elim⟩
    · simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at ha
      subst ha
      rfl
    · simp only [List.getLast?_singleton, Option.mem_def, Option.some.injEq] at ha
      subst ha
      rfl
  · subst h
    refine ⟨[], ?_⟩
    rw [M.vertexOf_sigma]
    exact isWalkFromTo_nil _

#audit_axioms GroupApproximation.Full.GL06p.walkReach_of_adjacent

/-- **Connected maps are walk-connected**: the equivalence closure of the elementary dart moves
is contained in walk reachability, since walks are reflexive, reverse and append. -/
theorem walkReach_of_eqvGen {d e : M.Dart} (h : Relation.EqvGen M.Adjacent d e) :
    WalkReach M d e := by
  induction h with
  | rel x y hxy => exact walkReach_of_adjacent M hxy
  | refl x => exact ⟨[], isWalkFromTo_nil _⟩
  | symm x y _ ih =>
    obtain ⟨l, hl⟩ := ih
    exact ⟨_, hl.reverse_map⟩
  | trans x y z _ _ ih₁ ih₂ =>
    obtain ⟨l₁, h₁⟩ := ih₁
    obtain ⟨l₂, h₂⟩ := ih₂
    exact ⟨_, h₁.append h₂⟩

#audit_axioms GroupApproximation.Full.GL06p.walkReach_of_eqvGen

end Reach

section Nearest

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- **A walk from the boundary to a relator cell** (Osin, proof of Lemma 9.7(b)): it starts at a
vertex of a dart of the outer face and ends at a vertex of a dart of the face of cell `j`. -/
def IsBoundaryToCellWalk (Delta : DiscDiagram.{u, w, v} W) (j : Fin Delta.rCellCount)
    (p : List Delta.toCombMap.Dart) : Prop :=
  ∃ a b : Delta.toCombMap.Dart, Delta.toCombMap.faceOf a = Delta.outerFace ∧
    Delta.toCombMap.faceOf b = (cell Delta j).face ∧
      IsWalkFromTo Delta.toCombMap p (Delta.toCombMap.vertexOf a) (Delta.toCombMap.vertexOf b)

/-- **Every relator cell is reached from the boundary** (Osin, proof of Lemma 9.7(b)): a disc
diagram is planar, so connected. -/
theorem exists_boundaryToCellWalk (Delta : DiscDiagram.{u, w, v} W)
    (j : Fin Delta.rCellCount) : ∃ p, IsBoundaryToCellWalk Delta j p := by
  obtain ⟨a, ha⟩ := Quotient.exists_rep Delta.outerFace
  obtain ⟨b, hb⟩ := Quotient.exists_rep (cell Delta j).face
  obtain ⟨p, hp⟩ := walkReach_of_eqvGen Delta.toCombMap
    (Delta.toCombMap.connected_of_planar Delta.planar a b)
  exact ⟨p, a, b, ha, hb, hp⟩

#audit_axioms GroupApproximation.Full.GL06p.exists_boundaryToCellWalk

/-- **A nearest cell with a minimal path** (Osin, proof of Lemma 9.7(b), "a cell `Π` nearest to
`∂Δ`, and a path `p` of minimal length from `∂Δ` to `∂Π`"): the path is no longer than any walk
from the boundary to any relator cell. -/
structure NearestCellPath (Delta : DiscDiagram.{u, w, v} W) where
  /-- The nearest cell `Π`. -/
  cell : Fin Delta.rCellCount
  /-- The minimal path `p`. -/
  path : List Delta.toCombMap.Dart
  walk : IsBoundaryToCellWalk Delta cell path
  minimal : ∀ (j : Fin Delta.rCellCount) (q : List Delta.toCombMap.Dart),
    IsBoundaryToCellWalk Delta j q → path.length ≤ q.length

/-- **A nearest cell and a minimal path exist** (Osin, proof of Lemma 9.7(b)) whenever the
diagram has a relator cell: take the least length realised by a walk from the boundary to some
relator cell. -/
theorem exists_nearestCellPath (Delta : DiscDiagram.{u, w, v} W) (h : 0 < Delta.rCellCount) :
    Nonempty (NearestCellPath Delta) := by
  classical
  have hex : ∃ n : ℕ, ∃ (j : Fin Delta.rCellCount) (q : List Delta.toCombMap.Dart),
      IsBoundaryToCellWalk Delta j q ∧ q.length = n := by
    obtain ⟨q, hq⟩ := exists_boundaryToCellWalk Delta ⟨0, h⟩
    exact ⟨q.length, ⟨0, h⟩, q, hq, rfl⟩
  obtain ⟨j, q, hq, hlen⟩ := Nat.find_spec hex
  refine ⟨⟨j, q, hq, fun j' q' hq' => ?_⟩⟩
  rw [hlen]
  exact Nat.find_min' hex ⟨j', q', hq', rfl⟩

#audit_axioms GroupApproximation.Full.GL06p.exists_nearestCellPath

end Nearest

end GroupApproximation.Full.GL06p
