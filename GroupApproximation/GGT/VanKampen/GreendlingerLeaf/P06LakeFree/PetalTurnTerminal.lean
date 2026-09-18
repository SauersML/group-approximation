import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.PetalTurnIndex
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.PetalSuccWalk
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P06, cactus petal: a closed walk turns or has a bad repeat (lane gl-p06-18)

Infrastructure for `P06LakeFree.PetalTurn.cellPocketLakeFreePetalTurn`
(`P06LakeFree/PetalTurnClose.lean`).  Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).

## Truth check

A closed vertex walk `W₀` (each `α W₀[i]` ends where `W₀[i + 1]` starts, cyclically) either turns
to its successors (`PetalSucc.SuccTurn`) or has two positions at one vertex where the walk can be
cut with a bad junction.  At a pinch vertex visited twice with good turns at both visits, the first
kept rotation from `α W₀[i]` is `W₀[i + 1]`, so no failure is reported there.

## The mathematical proof

Suppose position `i` fails: `x = σ^m (α W₀[i])` is the first kept rotation, `x ≠ W₀[j]` with
`j = (i + 1) % n`.  All of `x`, `α W₀[i]` and `W₀[j]` lie at one vertex.

1. *No turn into `W₀[j]`* (the step `hno`): if `σ (α W₀[k]) = W₀[j]` with `k + 1 = j`, then
   `k = i` and `σ¹ (α W₀[i])` is kept, so `m = 1` and `x = W₀[j]`.
2. *A second position at the vertex.*  If `x = W₀[q]`, then `q ≠ j`.  If `α x = W₀[r]`, take
   `q = (r + 1) % n`, at the vertex of `α W₀[r] = x`.  If `q = j`, then `r = i` and `σ^m` fixes
   `α W₀[i]`; `W₀[j] = σ^s (α W₀[i])` with `s < m` after reduction, and `s = 0` gives
   `x = W₀[j]` while `0 < s` contradicts firstness.
3. *The cut* (`exists_cut_of_lt`): cut at `min j q` and `max j q`.  The junction into `W₀[j]` has
   predecessor `W₀[j - 1]` (or none), which is bad by step 1.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.PetalTurn

open Embedded SimpleClosedWalkSides

universe u w v

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- The reverse of a dart of a closed vertex walk ends where the cyclically next dart begins. -/
theorem vertexOf_alpha_getElem {X : DiscDiagram.{u, w, v} W} {W₀ : List X.toCombMap.Dart}
    (hch : W₀.IsChain fun d e =>
      X.toCombMap.vertexOf (X.toCombMap.alpha d) = X.toCombMap.vertexOf e)
    (hcl : ∀ a ∈ W₀.getLast?, ∀ b ∈ W₀.head?,
      X.toCombMap.vertexOf (X.toCombMap.alpha a) = X.toCombMap.vertexOf b)
    {r : ℕ} (hr : r < W₀.length) :
    X.toCombMap.vertexOf (X.toCombMap.alpha W₀[r]) =
      X.toCombMap.vertexOf
        (W₀[(r + 1) % W₀.length]'(Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le r) hr))) := by
  rcases Nat.lt_or_ge (r + 1) W₀.length with h | h
  · exact (List.isChain_iff_getElem.mp hch r h).trans (congrArg X.toCombMap.vertexOf
      (P07InnerPocket.PocketRun.getElem_idx_congr W₀ (Nat.mod_eq_of_lt h).symm h _))
  · have hpos : 0 < W₀.length := Nat.lt_of_le_of_lt (Nat.zero_le r) hr
    have hmod : (r + 1) % W₀.length = 0 := by
      rw [show r + 1 = W₀.length by omega, Nat.mod_self]
    have hlast : W₀.length - 1 = r := by omega
    refine (hcl W₀[r] ?_ W₀[0] ?_).trans (congrArg X.toCombMap.vertexOf
      (P07InnerPocket.PocketRun.getElem_idx_congr W₀ hmod.symm hpos _))
    · rw [Option.mem_def, List.getLast?_eq_getElem?, hlast, getElem?_pos W₀ r hr]
    · rw [Option.mem_def, List.head?_eq_getElem?, getElem?_pos W₀ 0 hpos]

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.PetalTurn.vertexOf_alpha_getElem

/-- **A closed vertex walk turns to its successors, or can be cut at a bad repeated vertex.** -/
theorem succTurn_or_cut {X : DiscDiagram.{u, w, v} W} {W₀ : List X.toCombMap.Dart}
    (hch : W₀.IsChain fun d e =>
      X.toCombMap.vertexOf (X.toCombMap.alpha d) = X.toCombMap.vertexOf e)
    (hcl : ∀ a ∈ W₀.getLast?, ∀ b ∈ W₀.head?,
      X.toCombMap.vertexOf (X.toCombMap.alpha a) = X.toCombMap.vertexOf b) :
    PetalSucc.SuccTurn X W₀ ∨ ∃ (u : List X.toCombMap.Dart) (y : X.toCombMap.Dart)
      (B : List X.toCombMap.Dart) (y' : X.toCombMap.Dart) (v : List X.toCombMap.Dart),
      W₀ = u ++ y :: B ++ y' :: v ∧ X.toCombMap.vertexOf y = X.toCombMap.vertexOf y' ∧
      ¬ ((∃ x ∈ u.getLast?, X.toCombMap.sigma (X.toCombMap.alpha x) = y) ∧
        (∃ x ∈ (y :: B).getLast?, X.toCombMap.sigma (X.toCombMap.alpha x) = y')) := by
  refine or_iff_not_imp_left.mpr fun hS => ?_
  simp only [PetalSucc.SuccTurn, not_forall] at hS
  obtain ⟨i, hi, m, hm, hk, hf, hne⟩ := hS
  have hpos : 0 < W₀.length := Nat.lt_of_le_of_lt (Nat.zero_le i) hi
  obtain ⟨j, hjdef⟩ : ∃ j, j = (i + 1) % W₀.length := ⟨_, rfl⟩
  have hj : j < W₀.length := by
    rw [hjdef]
    exact Nat.mod_lt _ hpos
  have hne' : (X.toCombMap.sigma ^ m) (X.toCombMap.alpha W₀[i]) ≠ W₀[j] := fun h =>
    hne (h.trans (P07InnerPocket.PocketRun.getElem_idx_congr W₀ hjdef hj _))
  have hVj : X.toCombMap.vertexOf (X.toCombMap.alpha W₀[i]) = X.toCombMap.vertexOf W₀[j] :=
    (vertexOf_alpha_getElem hch hcl hi).trans (congrArg X.toCombMap.vertexOf
      (P07InnerPocket.PocketRun.getElem_idx_congr W₀ hjdef.symm _ hj))
  have hVx : X.toCombMap.vertexOf ((X.toCombMap.sigma ^ m) (X.toCombMap.alpha W₀[i])) =
      X.toCombMap.vertexOf W₀[j] :=
    (PetalSucc.petalSucc_vertexOf_sigma_pow X.toCombMap m _).trans hVj
  -- step 1: no turn into `W₀[j]`
  have hno : ∀ (k : ℕ) (hk' : k < W₀.length), k + 1 = j →
      X.toCombMap.sigma (X.toCombMap.alpha W₀[k]) ≠ W₀[j] := by
    intro k hk' hkj hσ
    have hki : i = k := succ_mod_eq_succ hi (hjdef.symm.trans hkj.symm)
    subst hki
    rcases Nat.lt_or_ge 1 m with h1 | h1
    · refine hf 1 Nat.one_pos h1 (Or.inl ?_)
      rw [pow_one, hσ]
      exact List.getElem_mem hj
    · have hm1 : m = 1 := by omega
      subst hm1
      exact hne' (by rw [pow_one]; exact hσ)
  -- step 2: a second position at the vertex
  obtain ⟨q, hq, hqj, hvq⟩ : ∃ (q : ℕ) (hq : q < W₀.length), q ≠ j ∧
      X.toCombMap.vertexOf W₀[q] = X.toCombMap.vertexOf W₀[j] := by
    rcases hk with hk | hk
    · obtain ⟨q, hq, hxq⟩ := List.getElem_of_mem hk
      refine ⟨q, hq, fun hqj =>
        hne' (hxq.symm.trans (P07InnerPocket.PocketRun.getElem_idx_congr W₀ hqj hq hj)), ?_⟩
      rw [hxq]
      exact hVx
    · obtain ⟨r, hr, hxr⟩ := List.getElem_of_mem hk
      refine ⟨(r + 1) % W₀.length, Nat.mod_lt _ hpos, fun hrj => ?_, ?_⟩
      · have hri : r = i := succ_mod_inj hr hi (hrj.trans hjdef)
        subst hri
        have hfix : (X.toCombMap.sigma ^ m) (X.toCombMap.alpha W₀[r]) =
            X.toCombMap.alpha W₀[r] := by
          have h := congrArg X.toCombMap.alpha hxr
          rw [X.toCombMap.alpha_involutive] at h
          exact h.symm
        obtain ⟨s, hs⟩ := ((X.toCombMap.vertexOf_eq_iff _ _).mp hVj).exists_nat_pow_eq
        have hs' : (X.toCombMap.sigma ^ (s % m)) (X.toCombMap.alpha W₀[r]) = W₀[j] :=
          (pow_mod_apply_of_pow_apply_eq_self X.toCombMap.sigma hfix s).trans hs
        rcases Nat.eq_zero_or_pos (s % m) with h0 | h0
        · rw [h0, pow_zero, Equiv.Perm.one_apply] at hs'
          exact hne' (hfix.trans hs')
        · refine hf (s % m) h0 (Nat.mod_lt s hm) (Or.inl ?_)
          rw [hs']
          exact List.getElem_mem hj
      · refine (vertexOf_alpha_getElem hch hcl hr).symm.trans ?_
        rw [hxr, X.toCombMap.alpha_involutive]
        exact hVx
  -- step 3: the cut
  rcases Nat.lt_or_gt_of_ne hqj with hlt | hlt
  · obtain ⟨u, B, v, heq, -, hB⟩ := exists_cut_of_lt W₀ hlt hj
    refine ⟨u, W₀[q], B, W₀[j], v, heq, hvq, ?_⟩
    rintro ⟨-, x, hx, hσ⟩
    obtain ⟨k, hk', hkj, rfl⟩ := hB x hx
    exact hno k hk' hkj hσ
  · obtain ⟨u, B, v, heq, hu, -⟩ := exists_cut_of_lt W₀ hlt hq
    refine ⟨u, W₀[j], B, W₀[q], v, heq, hvq.symm, ?_⟩
    rintro ⟨⟨x, hx, hσ⟩, -⟩
    obtain ⟨k, hk', hkj, rfl⟩ := hu x hx
    exact hno k hk' hkj hσ

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.PetalTurn.succTurn_or_cut

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.PetalTurn
