import GroupApproximation.GGT.VanKampen.ClosedWalkEnclosedSucc
import GroupApproximation.GGT.VanKampen.FaceSetBoundaryRotation
import Mathlib.Data.List.Rotate
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, inner pocket: enclosed face sets are invariant under rotation

Infrastructure for `P07LakeExclusion.InnerPocketEnclosedTwoArcStatement`
(`GreendlingerLeaf/P07LakeExclusion/InnerTwoArcLong.lean`), Osin, arXiv:math/0411039v3, §9, proof of
Lemma 9.7(b) (lane gl-p07-13).  The normal-form lane (gl-p07-14) moves the base point of the outer
walk of the filled pocket, so it needs that the outer walk of an `EnclosedFaceSetSucc` may be
rotated.

## The mathematical proof

Let `L' = L.rotate n` and `ℓ = |L|`.

1. *Membership.*  `d ∈ L' ↔ d ∈ L` (`List.mem_rotate`), hence `walkKeep M L' = walkKeep M L`.
   `ne_nil`, `nodup`, `mem_iff` and `turn_mem` only mention membership and `walkKeep`, so they
   transfer verbatim.
2. *Chain and closing step.*  A nonempty list that chains and closes along `R` chains and closes
   along `R` after any rotation: `Embedded.isChain_rotate_of_isChain_closes` and
   `Embedded.isChain_rotate_closing` (`FaceSetBoundaryRotation`).
3. *Successor turn.*  `L'[i] = L[(i + n) % ℓ]` (`List.getElem_rotate`).  Apply `turn_next` of `L`
   at `j = (i + n) % ℓ`; it yields `L[(j + 1) % ℓ]`, and
   `L'[(i + 1) % ℓ] = L[((i + 1) % ℓ + n) % ℓ]`.  Both indices equal `(i + n + 1) % ℓ`
   (`Nat.mod_add_mod`).
4. *Inverse walk.*  `invDarts X L = (L.reverse).map α`; `List.reverse_rotate` gives
   `(L.rotate n).reverse = L.reverse.rotate (ℓ - n % ℓ)` and `List.map_rotate` commutes the map.

Truth check: all four steps are list identities; the statement holds for every `n` (including
`n ≥ ℓ`, since everything is taken modulo `ℓ`).

* `EnclosedFaceSet.rotate`, `EnclosedFaceSetSucc.rotate`: the rotation invariance.
* `invDarts_rotate`: the inverse walk of a rotation.
* `EnclosedRotateStatement`, `enclosedRotate`: the lane-shaped statement and its proof.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

open Embedded SimpleClosedWalkSides

universe u w v

/-- Two entries of a list at equal indices are equal. -/
theorem getElem_index_congr {α : Type*} (l : List α) {a b : ℕ} (h : a = b)
    (ha : a < l.length) (hb : b < l.length) : l[a]'ha = l[b]'hb := by
  subst h
  rfl

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.getElem_index_congr

/-- The edges of a rotated walk are the edges of the walk. -/
theorem walkKeep_rotate_eq (M : CombMap.{v}) (L : List M.Dart) (n : ℕ) :
    walkKeep M (L.rotate n) = walkKeep M L := by
  funext d
  simp only [walkKeep, List.mem_rotate]

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.walkKeep_rotate_eq

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- The inverse walk of a rotated walk is a rotation of the inverse walk. -/
theorem invDarts_rotate (X : DiscDiagram.{u, w, v} W) (L : List X.toCombMap.Dart) (n : ℕ) :
    invDarts X (L.rotate n) = (invDarts X L).rotate (L.length - n % L.length) := by
  show (L.rotate n).reverse.map X.toCombMap.alpha =
    (L.reverse.map X.toCombMap.alpha).rotate (L.length - n % L.length)
  rw [List.reverse_rotate, List.map_rotate]

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.invDarts_rotate

/-- **An enclosed face set stays enclosed by any rotation of its outer walk.** -/
theorem EnclosedFaceSet.rotate {X : DiscDiagram.{u, w, v} W} {F : Finset X.toCombMap.Face}
    {L : List X.toCombMap.Dart} (E : EnclosedFaceSet X F L) (n : ℕ) :
    EnclosedFaceSet X F (L.rotate n) where
  outerFace_not_mem := E.outerFace_not_mem
  ne_nil := fun h => E.ne_nil (List.rotate_eq_nil_iff.mp h)
  nodup := List.nodup_rotate.mpr E.nodup
  chain := Embedded.isChain_rotate_of_isChain_closes E.ne_nil E.chain E.closes n
  closes := Embedded.isChain_rotate_closing E.ne_nil E.chain E.closes n
    (fun h => E.ne_nil (List.rotate_eq_nil_iff.mp h))
  mem_iff := by
    intro d
    simp only [List.mem_rotate]
    exact E.mem_iff d
  turn_mem := by
    intro d hd m hm hkeep hfirst
    rw [List.mem_rotate] at hd ⊢
    rw [walkKeep_rotate_eq] at hkeep
    rw [walkKeep_rotate_eq] at hfirst
    exact E.turn_mem d hd m hm hkeep hfirst

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.EnclosedFaceSet.rotate

/-- **An enclosed face set with successor turns stays so under any rotation of its outer walk.**
The entry of the rotation at `i` is the entry of the walk at `(i + n) % |L|`, and the successor
indices agree modulo `|L|`. -/
theorem EnclosedFaceSetSucc.rotate {X : DiscDiagram.{u, w, v} W} {F : Finset X.toCombMap.Face}
    {L : List X.toCombMap.Dart} (E : EnclosedFaceSetSucc X F L) (n : ℕ) :
    EnclosedFaceSetSucc X F (L.rotate n) where
  toEnclosedFaceSet := EnclosedFaceSet.rotate E.toEnclosedFaceSet n
  turn_next := by
    intro i hi m hm hkeep hfirst
    have hlen : 0 < L.length := List.length_pos_of_ne_nil E.ne_nil
    have hj : (i + n) % L.length < L.length := Nat.mod_lt _ hlen
    have hget : (L.rotate n)[i]'hi = L[(i + n) % L.length]'hj := List.getElem_rotate L n i hi
    rw [walkKeep_rotate_eq, hget] at hkeep
    rw [walkKeep_rotate_eq, hget] at hfirst
    rw [hget, E.turn_next ((i + n) % L.length) hj m hm hkeep hfirst, List.getElem_rotate]
    exact getElem_index_congr L
      (by rw [List.length_rotate, Nat.mod_add_mod, Nat.mod_add_mod, Nat.add_right_comm i n 1])
      _ _

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.EnclosedFaceSetSucc.rotate

/-- **Lane gl-p07-13, statement.**  Rotating the outer walk of an `EnclosedFaceSetSucc` gives an
`EnclosedFaceSetSucc` for the same faces, and its inverse walk is the matching rotation of the
inverse walk. -/
def EnclosedRotateStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (X : DiscDiagram.{u, w, v} W) (F : Finset X.toCombMap.Face) (L : List X.toCombMap.Dart),
    EnclosedFaceSetSucc X F L → ∀ n : ℕ,
      EnclosedFaceSetSucc X F (L.rotate n) ∧
        invDarts X (L.rotate n) = (invDarts X L).rotate (L.length - n % L.length)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.EnclosedRotateStatement

/-- **Lane gl-p07-13, proof.** -/
theorem enclosedRotate : EnclosedRotateStatement.{u, w, v} := by
  intro G _ Lambda W X F L E n
  exact ⟨EnclosedFaceSetSucc.rotate E n, invDarts_rotate X L n⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.enclosedRotate

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
