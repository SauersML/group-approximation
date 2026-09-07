import GroupApproximation.GGT.VanKampen.PermOrbitErasePoint

/-!
# Composing and constructing first-return permutations

Successive restrictions must retain the order of the ambient cycle, not just
its orbit equivalence relation. We prove uniqueness and composition of actual
first returns, and construct them on every embedded finite set by point erasure.
-/

namespace GroupApproximation.GGT.VanKampen.PermFirstReturn

open Equiv
universe u v w

/-- The first positive return determines the permutation uniquely. -/
theorem unique {A : Type u} {B : Type v} (p : Perm A) (q r : Perm B)
    (e : B ↪ A) (hq : IsFirstReturn p q e) (hr : IsFirstReturn p r e) : q = r := by
  apply Equiv.ext
  intro b
  obtain ⟨m, hm, hqm, hqs⟩ := hq b
  obtain ⟨n, hn, hrn, hrs⟩ := hr b
  have heq : m = n := by
    have hmn : ¬ m < n := fun h => hrs m hm h ⟨q b, hqm.symm⟩
    have hnm : ¬ n < m := fun h => hqs n hn h ⟨r b, hrn.symm⟩
    omega
  subst n
  exact e.injective (hqm.symm.trans hrn)

/-- Several first-return steps are one ambient iterate. Every earlier
ambient visit to the retained set is an earlier retained iterate, and a
positive ambient visit corresponds to a positive retained iterate. -/
theorem iterate {A : Type u} {B : Type v} (p : Perm A) (q : Perm B)
    (e : B ↪ A) (h : IsFirstReturn p q e) (n : ℕ) (b : B) :
    ∃ m : ℕ, n ≤ m ∧ (p ^ m) (e b) = e ((q ^ n) b) ∧
      ∀ k, k < m → (p ^ k) (e b) ∈ Set.range e →
        ∃ j, j < n ∧ (0 < k → 0 < j) ∧ (p ^ k) (e b) = e ((q ^ j) b) := by
  induction n generalizing b with
  | zero => exact ⟨0, le_rfl, rfl, by intro k hk; omega⟩
  | succ n ih =>
      obtain ⟨l, hl, hstep, hskip⟩ := h b
      obtain ⟨m, hm, hiter, htrace⟩ := ih (q b)
      refine ⟨m + l, by omega, ?_, ?_⟩
      · rw [pow_add, Perm.mul_apply, hstep, hiter, pow_succ, Perm.mul_apply]
      · intro k hk hke
        by_cases hk0 : k = 0
        · subst k
          exact ⟨0, by omega, by omega, rfl⟩
        · by_cases hkl : k < l
          · exact (hskip k (by omega) hkl hke).elim
          · have hle : l ≤ k := by omega
            have hshift : (p ^ (k - l)) (e (q b)) = (p ^ k) (e b) := by
              rw [← hstep, ← Perm.mul_apply, ← pow_add, Nat.sub_add_cancel hle]
            obtain ⟨j, hj, _, hje⟩ := htrace (k - l) (by omega) (by
              rw [hshift]
              exact hke)
            refine ⟨j + 1, by omega, by omega, ?_⟩
            rw [← hshift, hje, pow_succ, Perm.mul_apply]

/-- First return to a subset of a retained set agrees with first return
directly from the original permutation. -/
theorem trans {A : Type u} {B : Type v} {C : Type w}
    (p : Perm A) (q : Perm B) (r : Perm C) (e : B ↪ A) (f : C ↪ B)
    (hpq : IsFirstReturn p q e) (hqr : IsFirstReturn q r f) :
    IsFirstReturn p r (f.trans e) := by
  intro c
  obtain ⟨n, hn, hnext, hskip⟩ := hqr c
  obtain ⟨m, hm, hiter, htrace⟩ := iterate p q e hpq n (f c)
  refine ⟨m, by omega, ?_, ?_⟩
  · simpa only [Function.Embedding.trans_apply, hnext] using hiter
  · intro k hk hkm hke
    obtain ⟨c', hc'⟩ := hke
    obtain ⟨j, hj, hjpos, hje⟩ := htrace k hkm ⟨f c', hc'⟩
    apply hskip j (hjpos hk) hj
    exact ⟨c', e.injective (hc'.trans hje)⟩

/-- A bijective embedding needs just one ambient step. -/
theorem exists_of_surjective {A : Type u} {B : Type v} (p : Perm A)
    (e : B ↪ A) (he : Function.Surjective e) : ∃ q : Perm B, IsFirstReturn p q e := by
  let E : B ≃ A := Equiv.ofBijective e ⟨e.injective, he⟩
  let q : Perm B := Equiv.permCongr E.symm p
  refine ⟨q, fun b => ⟨1, by omega, ?_, by intro k hk hkn; omega⟩⟩
  change p (e b) = E (E.symm (p (E b)))
  exact (E.apply_symm_apply _).symm

/-- Every embedding into a finite permutation admits its actual first
return. The construction removes omitted points, and composition preserves
the full no-intermediate-return condition at every step. -/
theorem exists_firstReturn {A : Type u} [Fintype A] {B : Type v}
    (p : Perm A) (e : B ↪ A) : ∃ q : Perm B, IsFirstReturn p q e := by
  classical
  by_cases he : Function.Surjective e
  · exact exists_of_surjective p e he
  · change ¬ ∀ a, ∃ b, e b = a at he
    push Not at he
    obtain ⟨a, ha⟩ := he
    let e' : B ↪ {x : A // x ≠ a} :=
      ⟨fun b => ⟨e b, ha b⟩, fun b c h => e.injective (congrArg Subtype.val h)⟩
    obtain ⟨q, hq⟩ := exists_firstReturn (PermOrbitErasePoint.erase p a) e'
    refine ⟨q, ?_⟩
    have h := trans p (PermOrbitErasePoint.erase p a) q
      (Function.Embedding.subtype _) e' (PermOrbitErasePoint.firstReturn p a) hq
    have heq : e'.trans (Function.Embedding.subtype _) = e := by ext b; rfl
    rw [heq] at h
    exact h
termination_by Nat.card A
decreasing_by
  classical
  have hcard : Nat.card {x : A // x ≠ a} + 1 = Nat.card A := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_option]
      using Nat.card_congr (Equiv.optionSubtypeNe a)
  omega

/-- Factor a direct first return through an intermediate retained set.
Existence and uniqueness supply the intermediate permutation, so the full
order condition is preserved rather than assumed as a new input. -/
theorem of_trans {A : Type u} {B : Type v} [Finite B] {C : Type w}
    (p : Perm A) (q : Perm B) (r : Perm C) (e : B ↪ A) (f : C ↪ B)
    (hpq : IsFirstReturn p q e) (hpr : IsFirstReturn p r (f.trans e)) :
    IsFirstReturn q r f := by
  classical
  letI := Fintype.ofFinite B
  obtain ⟨s, hs⟩ := exists_firstReturn q f
  have heq := unique p s r (f.trans e) (trans p q s e f hpq hs) hpr
  rwa [heq] at hs

end GroupApproximation.GGT.VanKampen.PermFirstReturn

#audit_axioms GroupApproximation.GGT.VanKampen.PermFirstReturn.unique
#audit_axioms GroupApproximation.GGT.VanKampen.PermFirstReturn.trans
#audit_axioms GroupApproximation.GGT.VanKampen.PermFirstReturn.exists_firstReturn
#audit_axioms GroupApproximation.GGT.VanKampen.PermFirstReturn.of_trans
