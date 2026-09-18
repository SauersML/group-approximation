import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.PetalSuccWalk
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.PetalInvWalk
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P06, cactus petal: the inverse of a successor walk, no face set (gl-p06-17)

Infrastructure for `P06LakeFree.cellPocketLakeFreePetalSucc_of_petalTurn`
(`P06LakeFree/PetalSuccStatement.lean`).

## Truth check

`Petal.isNoncrossingClosedWalk_invDarts` (lane gl-p06-16) proves that `L = invDarts X W₀` is a
noncrossing closed walk from `EnclosedFaceSetSucc X F W₀` and no bridges.  Its proof uses only the
walk fields `ne_nil`, `nodup`, `chain`, `closes` and `turn_next`.  Here the same conclusion is
drawn from `W₀ ≠ []`, `W₀.Nodup`, `SuccTurn X W₀` and no bridges, with no face set: the chain and
closing come from `PetalSuccWalk.lean`.

## The mathematical proof

As in `PetalInvWalk.lean`, items 2-4: reading the chain of `W₀` backwards through `α` chains `L`;
the last dart of `L` is `α (head W₀)` and its first is `α (last W₀)`; if the first kept rotation
`x` from `α d` (for `d ∈ L`) were on `W₀`, say `x = W₀[j]` with cyclic predecessor `p`, then
`SuccTurn` and injectivity of first returns (`Petal.petal_firstKeep_inj`) give `d = W₀[p]`, a
bridge.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121) through Osin's Lemma 9.7(b); certifies no printed
sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.PetalSucc

open Embedded SimpleClosedWalkSides

universe u w v

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {X : DiscDiagram.{u, w, v} W} {W₀ : List X.toCombMap.Dart}

/-- The inverse of a successor walk chains. -/
theorem succTurn_chain_invDarts (hT : SuccTurn X W₀) :
    (invDarts X W₀).IsChain fun d e =>
      X.toCombMap.vertexOf (X.toCombMap.alpha d) = X.toCombMap.vertexOf e := by
  have hc : W₀.IsChain fun a b =>
      X.toCombMap.vertexOf (X.toCombMap.alpha (X.toCombMap.alpha b)) =
        X.toCombMap.vertexOf (X.toCombMap.alpha a) :=
    (succTurn_chain hT).imp fun a b h => by
      show X.toCombMap.vertexOf (X.toCombMap.alpha (X.toCombMap.alpha b)) =
        X.toCombMap.vertexOf (X.toCombMap.alpha a)
      rw [X.toCombMap.alpha_involutive b]
      exact h.symm
  show (W₀.reverse.map X.toCombMap.alpha).IsChain fun d e =>
    X.toCombMap.vertexOf (X.toCombMap.alpha d) = X.toCombMap.vertexOf e
  exact (List.isChain_map X.toCombMap.alpha).mpr (List.isChain_reverse.mpr hc)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.PetalSucc.succTurn_chain_invDarts

/-- The inverse of a successor walk closes up. -/
theorem succTurn_closes_invDarts (hT : SuccTurn X W₀) (hne : W₀ ≠ [])
    (hne' : invDarts X W₀ ≠ []) :
    X.toCombMap.vertexOf (X.toCombMap.alpha ((invDarts X W₀).getLast hne')) =
      X.toCombMap.vertexOf ((invDarts X W₀).head hne') := by
  have h1 : (invDarts X W₀).getLast hne' = X.toCombMap.alpha (W₀.head hne) := by
    simp only [invDarts, List.getLast_map, List.getLast_reverse]
  have h2 : (invDarts X W₀).head hne' = X.toCombMap.alpha (W₀.getLast hne) := by
    simp only [invDarts, List.head_map, List.head_reverse]
  rw [h1, h2, X.toCombMap.alpha_involutive (W₀.head hne)]
  exact (succTurn_closes hT hne).symm

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.PetalSucc.succTurn_closes_invDarts

/-- **Turning on the inverse of a successor walk without bridges.** -/
theorem succTurn_turn_mem_invDarts (hT : SuccTurn X W₀)
    (hα : ∀ d ∈ W₀, X.toCombMap.alpha d ∉ W₀) :
    ∀ d ∈ invDarts X W₀, ∀ m : ℕ, 0 < m →
      walkKeep X.toCombMap (invDarts X W₀) ((X.toCombMap.sigma ^ m) (X.toCombMap.alpha d)) →
      (∀ k, 0 < k → k < m → ¬ walkKeep X.toCombMap (invDarts X W₀)
        ((X.toCombMap.sigma ^ k) (X.toCombMap.alpha d))) →
      (X.toCombMap.sigma ^ m) (X.toCombMap.alpha d) ∈ invDarts X W₀ := by
  intro d hd m hm hkeep hfirst
  rw [Petal.petal_walkKeep_invDarts X W₀] at hkeep hfirst
  have hd' : X.toCombMap.alpha d ∈ W₀ := (Petal.petal_mem_invDarts_iff X).mp hd
  rw [Petal.petal_mem_invDarts_iff X]
  rcases hkeep with hx | hx
  · exfalso
    obtain ⟨j, hj, hxj⟩ := List.getElem_of_mem hx
    obtain ⟨p, hp, hidx⟩ := Petal.petal_exists_pred_index W₀ hj
    have hpmem : W₀[p] ∈ W₀ := List.getElem_mem hp
    obtain ⟨n, hn, hkeep', hfirst'⟩ := P07InnerPocket.PocketRun.exists_firstKeep W₀ hpmem
    have hx' : (X.toCombMap.sigma ^ n) (X.toCombMap.alpha W₀[p]) =
        (X.toCombMap.sigma ^ m) (X.toCombMap.alpha d) :=
      ((hT p hp n hn hkeep' hfirst').trans
        (P07InnerPocket.PocketRun.getElem_idx_congr W₀ hidx _ hj)).trans hxj
    have hpkeep : walkKeep X.toCombMap W₀ (X.toCombMap.alpha W₀[p]) :=
      Or.inr (by rw [X.toCombMap.alpha_involutive]; exact hpmem)
    have heq : X.toCombMap.alpha d = X.toCombMap.alpha W₀[p] :=
      Petal.petal_firstKeep_inj X.toCombMap W₀ (Or.inl hd') hpkeep hm hn hfirst hfirst' hx'.symm
    have hdW : d ∈ W₀ := by
      rw [X.toCombMap.alpha.injective heq]
      exact hpmem
    exact hα d hdW hd'
  · exact hx

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.PetalSucc.succTurn_turn_mem_invDarts

/-- **The inverse of a successor walk without bridges is a noncrossing closed walk.** -/
theorem succTurn_isNoncrossingClosedWalk_invDarts (hne : W₀ ≠ []) (hnd : W₀.Nodup)
    (hT : SuccTurn X W₀) (hα : ∀ d ∈ W₀, X.toCombMap.alpha d ∉ W₀) :
    IsNoncrossingClosedWalk X.toCombMap (invDarts X W₀) where
  ne_nil := by
    intro h
    unfold invDarts at h
    exact hne (List.reverse_eq_nil_iff.mp (List.map_eq_nil_iff.mp h))
  nodup := List.Nodup.map X.toCombMap.alpha.injective (List.nodup_reverse.mpr hnd)
  chain := succTurn_chain_invDarts hT
  closes := succTurn_closes_invDarts hT hne _
  alpha_not_mem := by
    intro d hd had
    rw [Petal.petal_mem_invDarts_iff X] at hd had
    rw [X.toCombMap.alpha_involutive d] at had
    exact hα d had hd
  turn_mem := succTurn_turn_mem_invDarts hT hα

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.PetalSucc.succTurn_isNoncrossingClosedWalk_invDarts

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.PetalSucc
