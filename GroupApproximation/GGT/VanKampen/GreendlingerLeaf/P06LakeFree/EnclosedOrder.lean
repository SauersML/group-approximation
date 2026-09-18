import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.Def
import GroupApproximation.GGT.VanKampen.NoncrossingClosedWalkSides
import GroupApproximation.GGT.VanKampen.ClosedWalkEnclosedSucc
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellFaceSet
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P06, Route B: the planar order of a lake-free pocket petal

Lane gl-p06-08 of `carto-gl-p06`.  Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b):
the subdiagram `Γ_1` with `∂Γ_1 = s_1 t_1 s_2 t_2`.  Target:
`P06LakeFree.CellPocketFaceSetLakeFreeEnclosedStatement` (`P06LakeFree/Statement.lean:77`).

## Truth check (on paper, before any Lean)

Write `K` for a cell pocket face set with `∂K = s₁ t̄₁ s₂ t̄₂` (`t̄₁ = Ā(Π_i)`, `t̄₂ = Ā(Π_j)`),
noncrossing boundary cycle, no lakes, and `C` a relator cell in `K.faces`.

* **The noncrossing hypothesis does NOT fix the list order at pinches.**
  `IsNoncrossingClosedWalk` only speaks about the dart set (the turn rule `turn_mem`), not the
  order in which the list `K.boundary.cycle` visits a vertex it meets three or more times.
* **FALSE: the whole face set as witness.**  Three petals `P₁, P₂, P₃` at a vertex, rotation order
  `P₁ P₂ P₃`, with `∂K` read `P₁ P₃ P₂`: `P₁ = s₁ᵃ`, `P₃ = s₁ᵇ t̄₁ s₂ᵃ`, `P₂ = s₂ᵇ t̄₂`.  The
  successor walk of `K.faces` reads `s₂ᵃ s₁ᵃ s₂ᵇ t̄₂ s₁ᵇ t̄₁`, so a side chunk has length up to `2ε`.
* **FALSE: the bare edge class of `C` with its lakes filled.**  Let `∂Π_i` have a loop `b` at a
  vertex `x` of the petal `P ∋ C`, with `t̄₁ = a b c`, `a, c ⊆ ∂P`.  The region cut off by `b` is
  bounded by boundary darts of `K`, so by lake freeness all its faces are in `K`; they form petals
  `Q` other than `P`, and they are no lake of `P` (crossing `b` into `Π_i` reaches the outside).
  The outer walk of `P` reads `…c̄ ā…`, so its `t̄₁`-part `a c` is not contiguous in `t̄₁`: no arc.
* **TRUE: the petal of `C` together with the petals cut off by loops of `∂Π_i`, `∂Π_j` at its
  vertices.**  Let `U` be this union and `L` its boundary walk.  Then:
  1. `sideFaces L = U ⊆ K.faces` and `C.face ∈ U`.  Every boundary edge of `U` is a boundary edge
     of `K` (a face of `K` across an edge of `U` is in the same edge class), and whole petals are
     added.
  2. `L` is noncrossing: around a vertex, the sectors of `U` are whole sectors of `K`, and deleting
     inner sectors from the alternating inner/outer pattern of `K` keeps the pattern.
  3. Filling the lakes of `U` adds no face off `K.faces` (lake freeness; this module,
     `enclosed_absorbed_subset_of_lakeFree`), and no face of `K` off `U`: such a petal has a
     boundary edge of `K`, facing the exterior piece of `K`, which is inside the exterior piece of
     `U` (`component_subset_of_subset`), and that edge is no boundary edge of `U`.  So `Π_i`, `Π_j`
     stay outside, and every dart of `L` faces the exterior piece.
  4. *Planar order.*  Lake freeness makes the petals meet like a cactus: two petals touching at two
     vertices enclose a region bounded by boundary darts of `K`, hence all in `K` (no lakes), hence
     joined to one of them across an edge, a contradiction.  So `U` is a disc glued along vertices
     and its successor walk visits the darts of `∂K` it keeps in the cyclic order of `∂K`: its
     inverse walk is a rotation of the filter `s₁' t₁' s₂' t₂'` of `s₁ t̄₁ s₂ t̄₂`, with
     `s₁' <+ s₁`, `s₂' <+ s₂`.
  5. *Contiguity.*  A piece of `t̄₁` leaving `U` between two darts of `U` is a closed sub-walk of
     `∂Π_i` at one vertex of `U` (two distinct vertices would again enclose a lake), that is, a
     loop, and its petals were added to `U`.  So `t₁'` is an infix of `t̄₁`, likewise `t₂'`.
* Verdict: the target is TRUE (as lane gl-p06-07 claims), but with the corrected witness `U` of the
  last item, not the edge class alone.  Without lake freeness it fails (case (d) of
  `Piece06.CellRoseLakesSurgeryBelowStatement`).

## Proof of the target from the order statement

`CellPocketLakeFreeEnclosedOrderStatement` (below) supplies items 1, 2, 4 and 5 for some
noncrossing `L`.  The proof of the target (`EnclosedOfOrder.lean`) then does the rest.
1. Fill the lakes of `sideFaces L` (`P07InnerPocket.exists_lakeFill_of_noncrossing`): an outer walk
   `W` with `EnclosedFaceSetSucc X F W`, `F = absorbed (sideFaces L) o`, and `C.face ∈ F`.
2. `F ⊆ K.faces` (`enclosed_absorbed_subset_of_lakeFree`), so `Π_i`, `Π_j`, `Π_i` again as `k₀`
   are off `F` (`K.first_not_mem`, `K.second_not_mem`).
3. The order statement gives `n` and `invDarts (W.rotate n) = s₁' ++ q₁ ++ s₂' ++ q₂`, with `q₁` a
   piece of `invDarts A(Π_i)` and `q₂` a piece of `invDarts A(Π_j)`.  Rotate
   (`P07InnerPocket.EnclosedFaceSetSucc.rotate`).
4. `q₁`, `q₂` read backwards arcs `B₁`, `B₂` (`P07InnerPocket.CyclicArc.exists_subArc_of_invDarts`).
5. `|s_t'| ≤ |s_t| ≤ ε` (`List.Sublist.length_le`, `K.firstSide_length_le`).
6. Merge into `A₁ = 0 ∨ 0 < A₂` (`P07InnerPocket.enclosedNormalForm`, lane gl-p07-14).

## Why the remaining statement is strictly smaller and true

It keeps only the planar content (items 1, 2, 4, 5 of the truth check): some noncrossing walk on
the side of `K` holding `C`, whose lake-filled successor walk is a rotated cyclic filter of `∂K`
with contiguous arc parts.  The lake filling, cells off the face set, sub-arcs, side bounds,
rotation and normal form are proved.  It is not the target restated: its conclusion names the
sides and arcs of `K` itself, and it asks nothing about relator cells, cell indices or `ε`.  The
clause is universal in the outer walk `W`, but `W` is determined up to rotation by its dart set
(`turn_next` picks the successor of a dart from the set), so this costs nothing.  No corpus lemma
gives the cactus order (item 4): lane gl-p07-10's order lemma is not on disk, and the Euler
noninterleaving tools need Euler hypotheses absent here.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

/-- **The planar order of a lake-free pocket petal** (remaining gap of lane gl-p06-08).  Under the
hypotheses of `CellPocketFaceSetLakeFreeEnclosedStatement`, there is a noncrossing closed walk `L`
whose side holds the relator cell `C` and lies in `K.faces`, such that every lake-filled successor
walk `W` of its side (as produced by `P07InnerPocket.exists_lakeFill_of_noncrossing`) reads, after
a rotation, `s₁' q₁ s₂' q₂`, where `s_t'` is a sub-list of the side `s_t` of `K` and `q₁`, `q₂` are
contiguous pieces of the backwards arcs `Ā(Π_i)`, `Ā(Π_j)` of `K`.
* **Why it is true.**  Take `L` the boundary walk of the petal of `C` together with the petals cut
  off by loops of `∂Π_i`, `∂Π_j` at its vertices.  Lake freeness makes the petals a cactus, so the
  successor walk is a cyclic filter of `∂K = s₁ t̄₁ s₂ t̄₂` with contiguous arc parts.  See the
  module docstring (the edge class alone is FALSE here, at loops of `∂Π_i`).
* **Why it is strictly smaller.**  Lake filling, cells off the face set, sub-arcs, side bounds,
  rotation and normal form are proved in `cellPocketFaceSetLakeFreeEnclosed_of_order`. -/
def CellPocketLakeFreeEnclosedOrderStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W)
    {i j : Fin X.rCellCount} (K : CellPocketFaceSet D eps X i j),
    i ≠ j →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    (∀ word ∈ W, 1 < word.length) →
    IsNoncrossingClosedWalk X.toCombMap K.boundary.cycle →
    CellPocketLakeFree K →
    ∀ C ∈ X.relatorCells, C.face ∈ K.faces →
      ∃ L : List X.toCombMap.Dart,
        IsNoncrossingClosedWalk X.toCombMap L ∧
          C.face ∈ sideFaces X.toCombMap L ∧
          sideFaces X.toCombMap L ⊆ K.faces ∧
          ∀ outerWalk : List X.toCombMap.Dart,
            EnclosedFaceSetSucc X
                (ExteriorComponent.absorbed X.toCombMap (sideFaces X.toCombMap L) X.outerFace)
                outerWalk →
            (∀ d : X.toCombMap.Dart, d ∈ outerWalk ↔ X.toCombMap.alpha d ∈ L ∧
              X.toCombMap.faceOf d ∈
                ExteriorComponent.component X.toCombMap (sideFaces X.toCombMap L) X.outerFace) →
            ∃ (n : ℕ) (p₁ q₁ r₁ p₂ q₂ r₂ s₁ s₂ : List X.toCombMap.Dart),
              invDarts X K.firstArc.darts = p₁ ++ q₁ ++ r₁ ∧
                invDarts X K.secondArc.darts = p₂ ++ q₂ ++ r₂ ∧
                s₁.Sublist K.firstSide ∧ s₂.Sublist K.secondSide ∧
                invDarts X (outerWalk.rotate n) = s₁ ++ q₁ ++ s₂ ++ q₂

section Absorbed

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- **Filling lakes inside a lake-free face set stays inside it.**  If `S ⊆ K.faces` and `K` is
lake free, then `absorbed S o ⊆ K.faces`: a face off `K.faces` lies in the exterior piece of `K`,
which is inside the exterior piece of `S` (`component_subset_of_subset`), so it is not absorbed. -/
theorem enclosed_absorbed_subset_of_lakeFree {K : CellPocketFaceSet D eps X i j}
    (hK : CellPocketLakeFree K) {S : Finset X.toCombMap.Face} (hsub : S ⊆ K.faces) :
    ExteriorComponent.absorbed X.toCombMap S X.outerFace ⊆ K.faces := by
  intro f hf
  by_contra hfK
  exact (ExteriorComponent.mem_absorbed_iff.mp hf)
    (component_subset_of_subset hsub K.outerFace_not_mem (hK f hfK))

end Absorbed

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.CellPocketLakeFreeEnclosedOrderStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.enclosed_absorbed_subset_of_lakeFree
