import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketRunStep
import Batteries.Data.List.Perm
import Mathlib.Data.List.Rotate
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-18: outer walks with the same darts are rotations

This is part (a) of lane gl-p07-18.  It is infrastructure for `PocketFourPieceLakeReadStatement`
(`FourPieceOffStatement.lean`), Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).

## Truth check

The statement is true, and it needs the membership hypothesis.  `EnclosedFaceSet.mem_iff` does not
fix the dart set from the face set alone: a bridge dart `d` with both sides outside the face set
satisfies `d ∈ l ↔ α d ∈ l`, so two walks over the same faces may differ on bridges.  With equal
dart sets, the two walks are rotations of each other.

## Proof

1. *A pure list lemma* (`eq_rotate_of_succ_compat`).  Take nodup lists `l₁`, `l₂` with the same
   members and `l₂ ≠ []`.  Assume that equal entries have equal cyclic successors.  Both lists
   are permutations of each other, so `|l₁| = |l₂| = ℓ`.  Pick `k` with `l₁[k] = l₂[0]`.  By
   induction on `t`, `l₂[t] = l₁[(t + k) % ℓ]`, and that is `(l₁.rotate k)[t]`.
2. *Successors from the dart set* (`EnclosedFaceSetSucc.eq_rotate_of_mem_iff`).  Equal members
   give `walkKeep l₁ = walkKeep l₂`.  `turn_next` says that the successor of `d` is `σ^m (α d)`,
   where `m` is the first index with `σ^m (α d)` kept (`PocketRun.exists_firstKeep`).  This depends
   only on `d` and `walkKeep`, so equal entries have equal successors.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121).  It certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

open Embedded SimpleClosedWalkSides

universe u w v

namespace LakeRead

/-- **Duplicate-free lists with the same members and compatible cyclic successors are
rotations.** -/
theorem eq_rotate_of_succ_compat {α : Type*} {l₁ l₂ : List α} (h₁ : l₁.Nodup) (h₂ : l₂.Nodup)
    (hmem : ∀ x, x ∈ l₁ ↔ x ∈ l₂) (hne : l₂ ≠ [])
    (hsucc : ∀ (i : ℕ) (hi : i < l₁.length) (j : ℕ) (hj : j < l₂.length), l₂[j] = l₁[i] →
      l₂[(j + 1) % l₂.length]'(Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le j) hj)) =
        l₁[(i + 1) % l₁.length]'(Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le i) hi))) :
    ∃ k, l₂ = l₁.rotate k := by
  have hlen : l₁.length = l₂.length :=
    ((List.perm_ext_iff_of_nodup h₁ h₂).mpr hmem).length_eq
  have h0 : 0 < l₂.length := List.length_pos_iff.mpr hne
  have hl1 : 0 < l₁.length := by omega
  obtain ⟨k, hk, hk0⟩ := List.getElem_of_mem ((hmem _).mpr (List.getElem_mem h0))
  have key : ∀ (t : ℕ) (ht : t < l₂.length),
      l₂[t]'ht = l₁[(t + k) % l₁.length]'(Nat.mod_lt _ hl1) := by
    intro t
    induction t with
    | zero =>
      intro ht
      have hidx : k = (0 + k) % l₁.length := by rw [Nat.zero_add, Nat.mod_eq_of_lt hk]
      exact hk0.symm.trans (PocketRun.getElem_idx_congr l₁ hidx hk _)
    | succ t ih =>
      intro ht
      have ht' : t < l₂.length := by omega
      have hstep := hsucc ((t + k) % l₁.length) (Nat.mod_lt _ hl1) t ht' (ih ht')
      refine (PocketRun.getElem_idx_congr l₂ (Nat.mod_eq_of_lt ht).symm ht _).trans
        (hstep.trans ?_)
      have hidx : ((t + k) % l₁.length + 1) % l₁.length = (t + 1 + k) % l₁.length := by
        rw [Nat.mod_add_mod, Nat.add_right_comm t k 1]
      exact PocketRun.getElem_idx_congr l₁ hidx _ _
  refine ⟨k, List.ext_getElem (by rw [List.length_rotate, hlen]) fun t ht _ => ?_⟩
  rw [List.getElem_rotate]
  exact key t ht

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.LakeRead.eq_rotate_of_succ_compat

end LakeRead

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {X : DiscDiagram.{u, w, v} W}

/-- Walks with the same darts keep the same edges. -/
theorem LakeRead.walkKeep_eq_of_mem_iff {l₁ l₂ : List X.toCombMap.Dart}
    (hmem : ∀ d, d ∈ l₁ ↔ d ∈ l₂) : walkKeep X.toCombMap l₂ = walkKeep X.toCombMap l₁ := by
  funext d
  simp only [walkKeep, hmem]

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.LakeRead.walkKeep_eq_of_mem_iff

/-- **Two outer walks with successor turns and the same darts are rotations of each other.**  The
face sets may differ: only `nodup`, `ne_nil` and `turn_next` are used. -/
theorem EnclosedFaceSetSucc.eq_rotate_of_mem_iff {F₁ F₂ : Finset X.toCombMap.Face}
    {l₁ l₂ : List X.toCombMap.Dart} (E₁ : EnclosedFaceSetSucc X F₁ l₁)
    (E₂ : EnclosedFaceSetSucc X F₂ l₂) (hmem : ∀ d, d ∈ l₁ ↔ d ∈ l₂) :
    ∃ k, l₂ = l₁.rotate k := by
  have hkeep := LakeRead.walkKeep_eq_of_mem_iff hmem
  refine LakeRead.eq_rotate_of_succ_compat E₁.nodup E₂.nodup hmem E₂.ne_nil ?_
  intro i hi j hj hij
  obtain ⟨m, hm, hk, hfirst⟩ := PocketRun.exists_firstKeep l₁ (List.getElem_mem hi)
  have h₁ := E₁.turn_next i hi m hm hk hfirst
  rw [← hij, ← hkeep] at hk hfirst
  have h₂ := E₂.turn_next j hj m hm hk hfirst
  have h₃ : (X.toCombMap.sigma ^ m) (X.toCombMap.alpha l₂[j]) =
      (X.toCombMap.sigma ^ m) (X.toCombMap.alpha l₁[i]) := by
    rw [hij]
  exact h₂.symm.trans (h₃.trans h₁)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.EnclosedFaceSetSucc.eq_rotate_of_mem_iff

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
