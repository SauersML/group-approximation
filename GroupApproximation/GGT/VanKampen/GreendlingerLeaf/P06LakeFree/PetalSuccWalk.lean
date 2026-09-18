import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketRunStep
import Mathlib.Data.List.Chain
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P06, cactus petal: walks turning to their successors (lane gl-p06-17)

Infrastructure for `P06LakeFree.cellPocketLakeFreePetalSucc_of_petalTurn`
(`P06LakeFree/PetalSuccStatement.lean`).  Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).

## Truth check

`SuccTurn X W₀` is the `turn_next` field of `EnclosedFaceSetSucc X F W₀`, with no face set: at
every position `i`, rotating from `α W₀[i]`, the first dart on an edge of `W₀` is `W₀[i + 1]`
(cyclically).  Every successor walk of `EnclosedFaceSetSucc` satisfies it.

## The mathematical proof

1. *Rotation keeps the vertex* (`petalSucc_vertexOf_sigma_pow`): induction on the power.
2. *Chain.*  For `i + 1 < |W₀|` there is a first kept rotation `σ^n (α W₀[i])`
   (`PocketRun.exists_firstKeep`); by `SuccTurn` it equals `W₀[i + 1]`, so
   `vertexOf (α W₀[i]) = vertexOf W₀[i + 1]`.
3. *Closing.*  The same at `i = |W₀| - 1`, where `(i + 1) % |W₀| = 0`.
4. *Turning.*  A dart `d ∈ W₀` is some `W₀[j]`; the first kept rotation from `α d` is
   `W₀[(j + 1) % |W₀|] ∈ W₀`.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121) through Osin's Lemma 9.7(b); certifies no printed
sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.PetalSucc

open Embedded SimpleClosedWalkSides

universe u w v

/-- Vertex rotation, iterated, keeps the vertex of a dart. -/
theorem petalSucc_vertexOf_sigma_pow (M : CombMap.{v}) (n : ℕ) (d : M.Dart) :
    M.vertexOf ((M.sigma ^ n) d) = M.vertexOf d := by
  induction n with
  | zero => rw [pow_zero, Equiv.Perm.one_apply]
  | succ n ih => rw [pow_succ', Equiv.Perm.mul_apply, M.vertexOf_sigma, ih]

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.PetalSucc.petalSucc_vertexOf_sigma_pow

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- **A dart walk turning to its successor**: at every position `i`, rotating from the reverse of
the dart at `i`, the first dart met on an edge of the walk is the dart at the next position.  This
is the `turn_next` field of `EnclosedFaceSetSucc`. -/
def SuccTurn (X : DiscDiagram.{u, w, v} W) (W₀ : List X.toCombMap.Dart) : Prop :=
  ∀ (i : ℕ) (hi : i < W₀.length) (m : ℕ), 0 < m →
    walkKeep X.toCombMap W₀ ((X.toCombMap.sigma ^ m) (X.toCombMap.alpha W₀[i])) →
    (∀ k, 0 < k → k < m → ¬ walkKeep X.toCombMap W₀
      ((X.toCombMap.sigma ^ k) (X.toCombMap.alpha W₀[i]))) →
    (X.toCombMap.sigma ^ m) (X.toCombMap.alpha W₀[i]) =
      W₀[(i + 1) % W₀.length]'(Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le i) hi))

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.PetalSucc.SuccTurn

variable {X : DiscDiagram.{u, w, v} W} {W₀ : List X.toCombMap.Dart}

/-- The reverse of a dart of a successor walk ends where the next dart begins. -/
theorem succTurn_vertexOf (hT : SuccTurn X W₀) {i : ℕ} (hi : i < W₀.length) :
    X.toCombMap.vertexOf (X.toCombMap.alpha W₀[i]) =
      X.toCombMap.vertexOf
        (W₀[(i + 1) % W₀.length]'(Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le i) hi))) := by
  obtain ⟨n, hn, hk, hf⟩ := P07InnerPocket.PocketRun.exists_firstKeep W₀ (List.getElem_mem hi)
  exact ((congrArg X.toCombMap.vertexOf (hT i hi n hn hk hf)).symm.trans
    (petalSucc_vertexOf_sigma_pow X.toCombMap n _)).symm

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.PetalSucc.succTurn_vertexOf

/-- A successor walk chains. -/
theorem succTurn_chain (hT : SuccTurn X W₀) :
    W₀.IsChain fun d e =>
      X.toCombMap.vertexOf (X.toCombMap.alpha d) = X.toCombMap.vertexOf e := by
  refine List.isChain_iff_getElem.mpr fun i hi => ?_
  have hi' : i < W₀.length := Nat.lt_of_succ_lt hi
  exact (succTurn_vertexOf hT hi').trans (congrArg X.toCombMap.vertexOf
    (P07InnerPocket.PocketRun.getElem_idx_congr W₀ (Nat.mod_eq_of_lt hi)
      (Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le i) hi')) hi))

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.PetalSucc.succTurn_chain

/-- A successor walk closes up. -/
theorem succTurn_closes (hT : SuccTurn X W₀) (hne : W₀ ≠ []) :
    X.toCombMap.vertexOf (X.toCombMap.alpha (W₀.getLast hne)) =
      X.toCombMap.vertexOf (W₀.head hne) := by
  have hpos : 0 < W₀.length := List.length_pos_iff.mpr hne
  have hl : W₀.length - 1 < W₀.length := Nat.sub_lt hpos Nat.one_pos
  have hmod : (W₀.length - 1 + 1) % W₀.length = 0 := by
    rw [Nat.sub_one_add_one hpos.ne', Nat.mod_self]
  rw [List.getLast_eq_getElem hne, List.head_eq_getElem hne]
  exact (succTurn_vertexOf hT hl).trans (congrArg X.toCombMap.vertexOf
    (P07InnerPocket.PocketRun.getElem_idx_congr W₀ hmod (Nat.mod_lt _ hpos) hpos))

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.PetalSucc.succTurn_closes

/-- A successor walk turns into itself. -/
theorem succTurn_turn_mem (hT : SuccTurn X W₀) :
    ∀ d ∈ W₀, ∀ m : ℕ, 0 < m →
      walkKeep X.toCombMap W₀ ((X.toCombMap.sigma ^ m) (X.toCombMap.alpha d)) →
      (∀ k, 0 < k → k < m → ¬ walkKeep X.toCombMap W₀
        ((X.toCombMap.sigma ^ k) (X.toCombMap.alpha d))) →
      (X.toCombMap.sigma ^ m) (X.toCombMap.alpha d) ∈ W₀ := by
  intro d hd m hm hk hf
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hd
  rw [hT j hj m hm hk hf]
  exact List.getElem_mem _

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.PetalSucc.succTurn_turn_mem

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.PetalSucc
