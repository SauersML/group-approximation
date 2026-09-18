import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketRunStep
import Batteries.Data.List.Perm
import Mathlib.Data.List.Rotate
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P06, cactus order: successor walks are unique up to rotation (lane gl-p06-14)

Infrastructure for `P06LakeFree.cellPocketLakeFreeEnclosedOrder_of_cactusOrder`
(`P06LakeFree/OrderCactusStatement.lean`).  The docstring of
`P06LakeFree.CellPocketLakeFreeEnclosedOrderStatement` notes that its universal clause over outer
walks "costs nothing"; this module proves it.

## The mathematical proof

Let `E : EnclosedFaceSetSucc X F ow` and `E' : EnclosedFaceSetSucc X F' ow'` with the same darts.

1. *Same edges.*  `walkKeep M w d = (d ∈ w ∨ α d ∈ w)` only mentions membership, so
   `walkKeep M ow = walkKeep M ow'` (`walkKeep_eq_of_mem_iff`).
2. *Same successor.*  If `ow[i] = ow'[i']`, pick the first `m > 0` with `σ^m (α ow[i])` kept
   (`P07InnerPocket.PocketRun.exists_firstKeep`).  `turn_next` of `E` gives
   `ow[i + 1] = σ^m (α ow[i])`, and, the edge sets being equal, `turn_next` of `E'` gives
   `ow'[i' + 1] = σ^m (α ow'[i'])` (indices modulo the lengths; `succ_eq_of_mem_iff`).
3. *Rotation.*  Both lists have no repeats and the same entries, so they have the same length
   (`List.perm_ext_iff_of_nodup`).  Let `ow[k] = ow'[0]`.  By induction with item 2,
   `ow'[i] = ow[(i + k) % |ow|]`, that is `ow' = ow.rotate k` (`List.getElem_rotate`).

Truth check: the face sets `F`, `F'` play no role; only `ne_nil`, `nodup` and `turn_next` are used.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.OrderCactus

open Embedded SimpleClosedWalkSides

universe u w v

/-- The edges of a walk only depend on its darts. -/
theorem walkKeep_eq_of_mem_iff (M : CombMap.{v}) {w₁ w₂ : List M.Dart}
    (h : ∀ d, d ∈ w₁ ↔ d ∈ w₂) : walkKeep M w₁ = walkKeep M w₂ := by
  funext d
  show (d ∈ w₁ ∨ M.alpha d ∈ w₁) = (d ∈ w₂ ∨ M.alpha d ∈ w₂)
  exact propext (or_congr (h d) (h (M.alpha d)))

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.OrderCactus.walkKeep_eq_of_mem_iff

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {X : DiscDiagram.{u, w, v} W} {F F' : Finset X.toCombMap.Face} {ow ow' : List X.toCombMap.Dart}

/-- **Successor walks with the same darts have the same successor.** -/
theorem succ_eq_of_mem_iff (E : EnclosedFaceSetSucc X F ow) (E' : EnclosedFaceSetSucc X F' ow')
    (hmem : ∀ d, d ∈ ow ↔ d ∈ ow') {i i' : ℕ} (hi : i < ow.length) (hi' : i' < ow'.length)
    (h : ow[i] = ow'[i']) :
    ow[(i + 1) % ow.length]'(Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le i) hi)) =
      ow'[(i' + 1) % ow'.length]'(Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le i') hi')) := by
  obtain ⟨m, hm, hkeep, hfirst⟩ :=
    P07InnerPocket.PocketRun.exists_firstKeep ow (List.getElem_mem hi)
  have hnext := E.turn_next i hi m hm hkeep hfirst
  have hk := walkKeep_eq_of_mem_iff X.toCombMap hmem
  rw [hk, h] at hkeep
  rw [hk, h] at hfirst
  rw [← hnext, h]
  exact E'.turn_next i' hi' m hm hkeep hfirst

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.OrderCactus.succ_eq_of_mem_iff

/-- **Successor walks with the same darts are rotations of each other.** -/
theorem exists_rotate_eq_of_mem_iff (E : EnclosedFaceSetSucc X F ow)
    (E' : EnclosedFaceSetSucc X F' ow') (hmem : ∀ d, d ∈ ow ↔ d ∈ ow') :
    ∃ k, ow' = ow.rotate k := by
  have hlen : ow.length = ow'.length :=
    ((List.perm_ext_iff_of_nodup E.nodup E'.nodup).2 hmem).length_eq
  have hpos' : 0 < ow'.length := List.length_pos_iff.2 E'.ne_nil
  obtain ⟨k, hk, hk0⟩ := List.getElem_of_mem ((hmem _).2 (List.getElem_mem hpos'))
  have hpos : 0 < ow.length := Nat.lt_of_le_of_lt (Nat.zero_le k) hk
  have key : ∀ (i : ℕ) (hi : i < ow'.length),
      ow'[i] = ow[(i + k) % ow.length]'(Nat.mod_lt _ hpos) := by
    intro i
    induction i with
    | zero =>
      intro _
      have hidx : k = (0 + k) % ow.length := by
        rw [Nat.zero_add]
        exact (Nat.mod_eq_of_lt hk).symm
      exact hk0.symm.trans
        (P07InnerPocket.PocketRun.getElem_idx_congr ow hidx hk (Nat.mod_lt _ hpos))
    | succ i ih =>
      intro hi
      have hi' : i < ow'.length := by omega
      have hs := succ_eq_of_mem_iff E E' hmem (Nat.mod_lt _ hpos) hi' (ih hi').symm
      have hidx : ((i + k) % ow.length + 1) % ow.length = (i + 1 + k) % ow.length := by
        rw [Nat.mod_add_mod, show i + k + 1 = i + 1 + k by omega]
      calc ow'[i + 1] = ow'[(i + 1) % ow'.length]'(Nat.mod_lt _ hpos') :=
            P07InnerPocket.PocketRun.getElem_idx_congr ow' (Nat.mod_eq_of_lt hi).symm hi
              (Nat.mod_lt _ hpos')
        _ = ow[((i + k) % ow.length + 1) % ow.length]'(Nat.mod_lt _ hpos) := hs.symm
        _ = ow[(i + 1 + k) % ow.length]'(Nat.mod_lt _ hpos) :=
            P07InnerPocket.PocketRun.getElem_idx_congr ow hidx (Nat.mod_lt _ hpos)
              (Nat.mod_lt _ hpos)
  refine ⟨k, List.ext_getElem ?_ ?_⟩
  · rw [List.length_rotate]
    exact hlen.symm
  · intro i h₁ _
    rw [List.getElem_rotate]
    exact key i h₁

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.OrderCactus.exists_rotate_eq_of_mem_iff

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.OrderCactus
