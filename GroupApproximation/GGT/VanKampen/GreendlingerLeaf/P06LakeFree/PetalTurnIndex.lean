import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.PetalTurnCutStep
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P06, cactus petal: index facts for the petal search (lane gl-p06-18)

Infrastructure for `P06LakeFree.PetalTurn.cellPocketLakeFreePetalTurn`
(`P06LakeFree/PetalTurnClose.lean`).  Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).

## The mathematical proof

1. *Cyclic successors* (`succ_mod_eq_succ`, `succ_mod_inj`): for `i, r < n`, `(i + 1) % n` is
   `i + 1` or `0`, so it determines `i`.
2. *Powers of a permutation fixing a point* (`pow_mod_apply_of_pow_apply_eq_self`): if
   `f^m d = d` then `f^s d = f^(s % m) d`, from `s = s % m + m * (s / m)`.
3. *Cutting a list at two positions* (`exists_cut_of_lt`): for `a < b < |l|`,
   `l = u ++ l[a] :: B ++ l[b] :: v`, where the last entry of `u` is `l[a - 1]` (if any) and the
   last entry of `l[a] :: B` is `l[b - 1]`.  Take `u = (l.take b).take a`,
   `B = (l.take b).drop (a + 1)` and `v = l.drop (b + 1)`.

Truth check: all items are elementary facts over any type.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.PetalTurn

/-- A cyclic successor that is a successor comes from the predecessor. -/
theorem succ_mod_eq_succ {n i k : ℕ} (hi : i < n) (h : (i + 1) % n = k + 1) : i = k := by
  rcases Nat.lt_or_ge (i + 1) n with h' | h'
  · rw [Nat.mod_eq_of_lt h'] at h
    omega
  · have hn : i + 1 = n := by omega
    rw [hn, Nat.mod_self] at h
    omega

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.PetalTurn.succ_mod_eq_succ

/-- The cyclic successor is injective. -/
theorem succ_mod_inj {n r i : ℕ} (hr : r < n) (hi : i < n) (h : (r + 1) % n = (i + 1) % n) :
    r = i := by
  rcases Nat.lt_or_ge (r + 1) n with h₁ | h₁ <;> rcases Nat.lt_or_ge (i + 1) n with h₂ | h₂
  · rw [Nat.mod_eq_of_lt h₁, Nat.mod_eq_of_lt h₂] at h
    omega
  · have hn : i + 1 = n := by omega
    rw [Nat.mod_eq_of_lt h₁, hn, Nat.mod_self] at h
    omega
  · have hn : r + 1 = n := by omega
    rw [hn, Nat.mod_self, Nat.mod_eq_of_lt h₂] at h
    omega
  · omega

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.PetalTurn.succ_mod_inj

/-- Powers of a permutation fixing a point through a power reduce modulo that power. -/
theorem pow_mod_apply_of_pow_apply_eq_self {β : Type*} (f : Equiv.Perm β) {m : ℕ} {d : β}
    (hfix : (f ^ m) d = d) (s : ℕ) : (f ^ (s % m)) d = (f ^ s) d := by
  calc (f ^ (s % m)) d = (f ^ (s % m)) (((f ^ m) ^ (s / m)) d) := by
        rw [Equiv.Perm.pow_apply_eq_self_of_apply_eq_self hfix]
    _ = (f ^ (s % m + m * (s / m))) d := by
        rw [pow_add, pow_mul, Equiv.Perm.mul_apply]
    _ = (f ^ s) d := by rw [Nat.mod_add_div]

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.PetalTurn.pow_mod_apply_of_pow_apply_eq_self

variable {α : Type*}

/-- The last entry of a nonempty prefix. -/
theorem getLast?_take_succ (l : List α) {c : ℕ} (hc : c < l.length) :
    (l.take (c + 1)).getLast? = some l[c] := by
  rw [← List.take_append_getElem hc, List.getLast?_concat]

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.PetalTurn.getLast?_take_succ

/-- **Cutting a list at two positions.** -/
theorem exists_cut_of_lt (l : List α) {a b : ℕ} (hab : a < b) (hb : b < l.length) :
    ∃ u B v : List α, l = u ++ l[a]'(Nat.lt_trans hab hb) :: B ++ l[b] :: v ∧
      (∀ x ∈ u.getLast?, ∃ k, ∃ hk : k < l.length, k + 1 = a ∧ x = l[k]) ∧
      (∀ x ∈ (l[a]'(Nat.lt_trans hab hb) :: B).getLast?,
        ∃ k, ∃ hk : k < l.length, k + 1 = b ∧ x = l[k]) := by
  obtain ⟨d, rfl⟩ : ∃ d, b = d + 1 := ⟨b - 1, by omega⟩
  have hd : d < l.length := by omega
  have haL : a < (l.take (d + 1)).length := by
    rw [List.length_take]
    omega
  have hLa : (l.take (d + 1))[a]'haL = l[a]'(Nat.lt_trans hab hb) := List.getElem_take
  have hnot : ¬ (l.take (d + 1)).length ≤ a := by
    rw [List.length_take]
    omega
  refine ⟨(l.take (d + 1)).take a, (l.take (d + 1)).drop (a + 1), l.drop (d + 1 + 1), ?_, ?_, ?_⟩
  · rw [← hLa, List.getElem_cons_drop, List.getElem_cons_drop, List.take_append_drop,
      List.take_append_drop]
  · intro x hx
    cases a with
    | zero => simp at hx
    | succ c =>
      have hc : c < (l.take (d + 1)).length := by
        rw [List.length_take]
        omega
      rw [getLast?_take_succ _ hc, Option.mem_def, Option.some.injEq] at hx
      exact ⟨c, by omega, rfl, by rw [← hx, List.getElem_take]⟩
  · intro x hx
    rw [← hLa, List.getElem_cons_drop, List.getLast?_drop, if_neg hnot, getLast?_take_succ l hd,
      Option.mem_def, Option.some.injEq] at hx
    exact ⟨d, hd, rfl, hx.symm⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.PetalTurn.exists_cut_of_lt

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.PetalTurn
