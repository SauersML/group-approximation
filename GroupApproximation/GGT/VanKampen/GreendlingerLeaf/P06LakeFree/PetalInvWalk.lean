import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketRunStep
import GroupApproximation.GGT.VanKampen.NoncrossingClosedWalkSides
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Nodup
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P06, cactus petal: the inverse of a successor walk is noncrossing (gl-p06-16)

Infrastructure for `P06LakeFree.cellPocketLakeFreeCactusPetal_of_petalSucc`
(`P06LakeFree/PetalStatement.lean`).

## The mathematical proof

Let `E₀ : EnclosedFaceSetSucc X F W₀` and assume no dart of `W₀` has its reverse on `W₀`
(no bridges).  Put `L = invDarts X W₀ = map α (reverse W₀)`.

1. *Membership.*  `e ∈ L ↔ α e ∈ W₀` (`α` is an involution), so `walkKeep L = walkKeep W₀`.
2. *Walk fields.*  `L ≠ []` and `L` has no repeats (`α` is injective).  The chain relation
   `vertexOf (α d) = vertexOf e` of `W₀` read backwards through `α` is the chain relation of `L`:
   for consecutive `a, b` of `W₀`, `L` has `α b, α a`, and `vertexOf (α (α b)) = vertexOf b =
   vertexOf (α a)`.  Closing: the last dart of `L` is `α (head W₀)`, its first dart is
   `α (last W₀)`, and `vertexOf (head W₀) = vertexOf (α (last W₀))` is `E₀.closes`.
3. *No reverse.*  `e, α e ∈ L` means `α e, e ∈ W₀`, excluded by assumption.
4. *Turning.*  Let `d ∈ L`, so `α d ∈ W₀`, and let `m > 0` be the first index with
   `x = σ^m (α d)` kept.  If `α x ∈ W₀` then `x ∈ L`.  Otherwise `x ∈ W₀`, say `x = W₀[j]`.
   Let `p` be the cyclic predecessor of `j` (`(p + 1) % |W₀| = j`) and `n > 0` the first index
   with `σ^n (α W₀[p])` kept.  `turn_next` gives `σ^n (α W₀[p]) = W₀[j] = x = σ^m (α d)`.
   *First returns are injective* (`petal_firstKeep_inj`): if `σ^m y = σ^n z` with both `y, z`
   kept and `m`, `n` first returns, then `m = n` (if `m < n`, `σ^(n-m) z = y` is kept with `0 < n - m < n`),
   so `y = z`.  Hence `α d = α W₀[p]`, `d = W₀[p] ∈ W₀`, while `α d ∈ W₀`: a bridge, excluded.

So `L` is a noncrossing closed walk (`isNoncrossingClosedWalk_invDarts`).

## Manuscript status

Infrastructure for `thm:hull` (tex 2121) through Osin's Lemma 9.7(b); certifies no printed
sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.Petal

open Embedded SimpleClosedWalkSides

universe u w v

/-- Rotating `m ≤ n` steps first: a common image gives a rotation between the starting darts. -/
theorem petal_sigma_pow_sub_eq (M : CombMap.{v}) {y z : M.Dart} {m n : ℕ} (hmn : m ≤ n)
    (h : (M.sigma ^ m) y = (M.sigma ^ n) z) : (M.sigma ^ (n - m)) z = y := by
  apply (M.sigma ^ m).injective
  rw [← Equiv.Perm.mul_apply (M.sigma ^ m) (M.sigma ^ (n - m)) z, ← pow_add,
    Nat.add_sub_of_le hmn]
  exact h.symm

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.Petal.petal_sigma_pow_sub_eq

/-- **First returns to the edges of a walk are injective.** -/
theorem petal_firstKeep_inj (M : CombMap.{v}) (w : List M.Dart) {y z : M.Dart}
    (hy : walkKeep M w y) (hz : walkKeep M w z) {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hfy : ∀ k, 0 < k → k < m → ¬ walkKeep M w ((M.sigma ^ k) y))
    (hfz : ∀ k, 0 < k → k < n → ¬ walkKeep M w ((M.sigma ^ k) z))
    (h : (M.sigma ^ m) y = (M.sigma ^ n) z) : y = z := by
  rcases lt_trichotomy m n with hlt | heq | hgt
  · have hs := petal_sigma_pow_sub_eq M hlt.le h
    exact (hfz (n - m) (by omega) (by omega) (by rw [hs]; exact hy)).elim
  · subst heq
    exact (M.sigma ^ m).injective h
  · have hs := petal_sigma_pow_sub_eq M hgt.le h.symm
    exact (hfy (m - n) (by omega) (by omega) (by rw [hs]; exact hz)).elim

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.Petal.petal_firstKeep_inj

/-- Every position of a nonempty list has a cyclic predecessor. -/
theorem petal_exists_pred_index {α : Type*} (l : List α) {j : ℕ} (hj : j < l.length) :
    ∃ p, p < l.length ∧ (p + 1) % l.length = j := by
  have hpos : 0 < l.length := Nat.lt_of_le_of_lt (Nat.zero_le j) hj
  refine ⟨(j + l.length - 1) % l.length, Nat.mod_lt _ hpos, ?_⟩
  rw [Nat.mod_add_mod, show j + l.length - 1 + 1 = j + l.length by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt hj]

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.Petal.petal_exists_pred_index

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- Membership in the inverse walk. -/
theorem petal_mem_invDarts_iff (X : DiscDiagram.{u, w, v} W) {l : List X.toCombMap.Dart}
    {e : X.toCombMap.Dart} : e ∈ invDarts X l ↔ X.toCombMap.alpha e ∈ l := by
  unfold invDarts
  rw [List.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [X.toCombMap.alpha_involutive x]
    exact List.mem_reverse.mp hx
  · intro h
    exact ⟨X.toCombMap.alpha e, List.mem_reverse.mpr h, X.toCombMap.alpha_involutive e⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.Petal.petal_mem_invDarts_iff

/-- The inverse walk twice is the walk. -/
theorem petal_invDarts_invDarts (X : DiscDiagram.{u, w, v} W) (l : List X.toCombMap.Dart) :
    invDarts X (invDarts X l) = l := by
  simp only [invDarts, List.map_reverse, List.reverse_reverse, List.map_map,
    X.toCombMap.alpha_involutive.comp_self, List.map_id]

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.Petal.petal_invDarts_invDarts

/-- The inverse walk has the edges of the walk. -/
theorem petal_walkKeep_invDarts (X : DiscDiagram.{u, w, v} W) (l : List X.toCombMap.Dart) :
    walkKeep X.toCombMap (invDarts X l) = walkKeep X.toCombMap l := by
  funext d
  show (d ∈ invDarts X l ∨ X.toCombMap.alpha d ∈ invDarts X l) =
    (d ∈ l ∨ X.toCombMap.alpha d ∈ l)
  rw [petal_mem_invDarts_iff X, petal_mem_invDarts_iff X, X.toCombMap.alpha_involutive d]
  exact propext or_comm

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.Petal.petal_walkKeep_invDarts

variable {X : DiscDiagram.{u, w, v} W} {F : Finset X.toCombMap.Face} {W₀ : List X.toCombMap.Dart}

/-- The inverse of an enclosing walk chains. -/
theorem petal_chain_invDarts (E₀ : EnclosedFaceSet X F W₀) :
    (invDarts X W₀).IsChain fun d e =>
      X.toCombMap.vertexOf (X.toCombMap.alpha d) = X.toCombMap.vertexOf e := by
  have hc : W₀.IsChain fun a b =>
      X.toCombMap.vertexOf (X.toCombMap.alpha (X.toCombMap.alpha b)) =
        X.toCombMap.vertexOf (X.toCombMap.alpha a) :=
    E₀.chain.imp fun a b h => by
      show X.toCombMap.vertexOf (X.toCombMap.alpha (X.toCombMap.alpha b)) =
        X.toCombMap.vertexOf (X.toCombMap.alpha a)
      rw [X.toCombMap.alpha_involutive b]
      exact h.symm
  show (W₀.reverse.map X.toCombMap.alpha).IsChain fun d e =>
    X.toCombMap.vertexOf (X.toCombMap.alpha d) = X.toCombMap.vertexOf e
  exact (List.isChain_map X.toCombMap.alpha).mpr (List.isChain_reverse.mpr hc)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.Petal.petal_chain_invDarts

/-- The inverse of an enclosing walk closes up. -/
theorem petal_closes_invDarts (E₀ : EnclosedFaceSet X F W₀) (hne : invDarts X W₀ ≠ []) :
    X.toCombMap.vertexOf (X.toCombMap.alpha ((invDarts X W₀).getLast hne)) =
      X.toCombMap.vertexOf ((invDarts X W₀).head hne) := by
  have h1 : (invDarts X W₀).getLast hne = X.toCombMap.alpha (W₀.head E₀.ne_nil) := by
    simp only [invDarts, List.getLast_map, List.getLast_reverse]
  have h2 : (invDarts X W₀).head hne = X.toCombMap.alpha (W₀.getLast E₀.ne_nil) := by
    simp only [invDarts, List.head_map, List.head_reverse]
  rw [h1, h2, X.toCombMap.alpha_involutive (W₀.head E₀.ne_nil)]
  exact E₀.closes.symm

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.Petal.petal_closes_invDarts

/-- **Turning on the inverse walk.**  The first kept dart after the reverse of a dart of the
inverse walk is on the inverse walk, when the walk has no bridges. -/
theorem petal_turn_mem_invDarts (E₀ : EnclosedFaceSetSucc X F W₀)
    (hα : ∀ d ∈ W₀, X.toCombMap.alpha d ∉ W₀) :
    ∀ d ∈ invDarts X W₀, ∀ m : ℕ, 0 < m →
      walkKeep X.toCombMap (invDarts X W₀) ((X.toCombMap.sigma ^ m) (X.toCombMap.alpha d)) →
      (∀ k, 0 < k → k < m → ¬ walkKeep X.toCombMap (invDarts X W₀)
        ((X.toCombMap.sigma ^ k) (X.toCombMap.alpha d))) →
      (X.toCombMap.sigma ^ m) (X.toCombMap.alpha d) ∈ invDarts X W₀ := by
  intro d hd m hm hkeep hfirst
  rw [petal_walkKeep_invDarts X W₀] at hkeep hfirst
  have hd' : X.toCombMap.alpha d ∈ W₀ := (petal_mem_invDarts_iff X).mp hd
  rw [petal_mem_invDarts_iff X]
  rcases hkeep with hx | hx
  · exfalso
    obtain ⟨j, hj, hxj⟩ := List.getElem_of_mem hx
    obtain ⟨p, hp, hidx⟩ := petal_exists_pred_index W₀ hj
    have hpmem : W₀[p] ∈ W₀ := List.getElem_mem hp
    obtain ⟨n, hn, hkeep', hfirst'⟩ := P07InnerPocket.PocketRun.exists_firstKeep W₀ hpmem
    have hnext := E₀.turn_next p hp n hn hkeep' hfirst'
    have hx' : (X.toCombMap.sigma ^ n) (X.toCombMap.alpha W₀[p]) =
        (X.toCombMap.sigma ^ m) (X.toCombMap.alpha d) :=
      (hnext.trans (P07InnerPocket.PocketRun.getElem_idx_congr W₀ hidx _ hj)).trans hxj
    have hpkeep : walkKeep X.toCombMap W₀ (X.toCombMap.alpha W₀[p]) :=
      Or.inr (by rw [X.toCombMap.alpha_involutive]; exact hpmem)
    have heq : X.toCombMap.alpha d = X.toCombMap.alpha W₀[p] :=
      petal_firstKeep_inj X.toCombMap W₀ (Or.inl hd') hpkeep hm hn hfirst hfirst' hx'.symm
    have hdW : d ∈ W₀ := by
      rw [X.toCombMap.alpha.injective heq]
      exact hpmem
    exact hα d hdW hd'
  · exact hx

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.Petal.petal_turn_mem_invDarts

/-- **The inverse of a successor walk without bridges is a noncrossing closed walk.** -/
theorem isNoncrossingClosedWalk_invDarts (E₀ : EnclosedFaceSetSucc X F W₀)
    (hα : ∀ d ∈ W₀, X.toCombMap.alpha d ∉ W₀) :
    IsNoncrossingClosedWalk X.toCombMap (invDarts X W₀) where
  ne_nil := by
    intro h
    unfold invDarts at h
    exact E₀.ne_nil (List.reverse_eq_nil_iff.mp (List.map_eq_nil_iff.mp h))
  nodup := List.Nodup.map X.toCombMap.alpha.injective (List.nodup_reverse.mpr E₀.nodup)
  chain := petal_chain_invDarts E₀.toEnclosedFaceSet
  closes := petal_closes_invDarts E₀.toEnclosedFaceSet _
  alpha_not_mem := by
    intro d hd had
    rw [petal_mem_invDarts_iff X] at hd had
    rw [X.toCombMap.alpha_involutive d] at had
    exact hα d had hd
  turn_mem := petal_turn_mem_invDarts E₀ hα

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.Petal.isNoncrossingClosedWalk_invDarts

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.Petal
