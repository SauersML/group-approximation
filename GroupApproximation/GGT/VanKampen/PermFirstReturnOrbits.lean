import GroupApproximation.GGT.VanKampen.CombMap
import GroupApproximation.Meta.AxiomGuard

/-!
# Orbits of an actual first-return permutation

If each step of a permutation on retained points is the first positive return
of an ambient permutation, its orbits are exactly the ambient orbits meeting
the retained set. The first-return condition includes absence of intermediate
retained points; merely mapping each step into an ambient orbit would not
prove the converse. Region surgery supplies this condition from its boundary
walk, without an orbit-equivalence input.
-/

namespace GroupApproximation.GGT.VanKampen.PermFirstReturn

open Equiv
universe u v

/-- Every new step is the first positive ambient step returning to the image. -/
def IsFirstReturn {A : Type u} {B : Type v} (p : Perm A) (q : Perm B)
    (e : B ↪ A) : Prop :=
  ∀ b, ∃ m : ℕ, 0 < m ∧ (p ^ m) (e b) = e (q b) ∧
    ∀ k, 0 < k → k < m → (p ^ k) (e b) ∉ Set.range e

/-- The first-return permutation neither splits nor joins retained ambient
orbits. -/
theorem sameCycle_iff {A : Type u} {B : Type v} [Finite A] [Finite B]
    (p : Perm A) (q : Perm B) (e : B ↪ A) (h : IsFirstReturn p q e)
    (a b : B) : q.SameCycle a b ↔ p.SameCycle (e a) (e b) := by
  constructor
  · intro hab
    obtain ⟨n, hn⟩ := hab.exists_nat_pow_eq
    have hp : ∀ (n : ℕ) (a : B), p.SameCycle (e a) (e ((q ^ n) a)) := by
      intro n
      induction n with
      | zero => intro a; exact Perm.SameCycle.rfl
      | succ n ih =>
          intro a
          rw [pow_succ, Perm.mul_apply]
          obtain ⟨m, _, hm, _⟩ := h a
          have hs : p.SameCycle (e a) (e (q a)) :=
            ⟨(m : ℤ), by simpa only [zpow_natCast] using hm⟩
          exact hs.trans (ih (q a))
    simpa only [hn] using hp n a
  · intro hab
    obtain ⟨n, hn⟩ := hab.exists_nat_pow_eq
    have hp : ∀ (n : ℕ) (a b : B), (p ^ n) (e a) = e b → q.SameCycle a b := by
      intro n
      induction n using Nat.strong_induction_on with
      | h n ih =>
          intro a b hn
          by_cases hz : n = 0
          · subst n
            have he : e a = e b := by simpa using hn
            exact (e.injective he).sameCycle q
          · obtain ⟨m, hm, hnext, hskip⟩ := h a
            have hmn : m ≤ n := by
              by_contra hlt
              exact hskip n (Nat.pos_of_ne_zero hz) (by omega) ⟨b, hn.symm⟩
            have hrest : (p ^ (n - m)) (e (q a)) = e b := by
              rw [← hnext, ← Perm.mul_apply, ← pow_add, Nat.sub_add_cancel hmn]
              exact hn
            exact (Perm.SameCycle.rfl.apply_right).trans
              (ih (n - m) (by omega) (q a) b hrest)
    exact hp n a b hn

/-- The orbit map induced by retaining points. -/
def orbitMap {A : Type u} {B : Type v} [Finite A] [Finite B]
    (p : Perm A) (q : Perm B) (e : B ↪ A) (h : IsFirstReturn p q e) :
    CombMap.Orbit q → CombMap.Orbit p :=
  Quotient.map e fun a b hab => (sameCycle_iff p q e h a b).mp hab

theorem orbitMap_injective {A : Type u} {B : Type v} [Finite A] [Finite B]
    (p : Perm A) (q : Perm B) (e : B ↪ A) (h : IsFirstReturn p q e) :
    Function.Injective (orbitMap p q e h) := by
  intro a b
  refine Quotient.inductionOn₂ a b ?_
  intro a b hab
  exact Quotient.sound ((sameCycle_iff p q e h a b).mpr (Quotient.exact hab))

/-- Orbits after first return are the old orbits containing a retained point. -/
noncomputable def orbitEquiv {A : Type u} {B : Type v} [Finite A] [Finite B]
    (p : Perm A) (q : Perm B) (e : B ↪ A) (h : IsFirstReturn p q e) :
    CombMap.Orbit q ≃
      {c : CombMap.Orbit p // ∃ b : B, Quotient.mk'' (e b) = c} := by
  let f : CombMap.Orbit q →
      {c : CombMap.Orbit p // ∃ b : B, Quotient.mk'' (e b) = c} := fun c =>
    ⟨orbitMap p q e h c, by
      induction c using Quotient.inductionOn' with
      | h b => exact ⟨b, rfl⟩⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro a b hab
    exact orbitMap_injective p q e h (congrArg Subtype.val hab)
  · rintro ⟨c, b, hb⟩
    refine ⟨Quotient.mk'' b, ?_⟩
    exact Subtype.ext hb

/-- A walk whose nonterminal points are deleted is a finite iterate, and all
strictly earlier iterates are deleted. -/
theorem exists_pow_of_skip_walk {A : Type u} (p : Perm A) (deleted : A → Prop)
    {a b : A}
    (h : Relation.ReflTransGen (fun x y => deleted x ∧ p x = y) a b) :
    ∃ n : ℕ, (p ^ n) a = b ∧ ∀ k, k < n → deleted ((p ^ k) a) := by
  induction h with
  | refl => exact ⟨0, rfl, by omega⟩
  | @tail b c hab hbc ih =>
      obtain ⟨n, hn, hskip⟩ := ih
      refine ⟨n + 1, ?_, ?_⟩
      · rw [pow_succ', Perm.mul_apply, hn]
        exact hbc.2
      · intro k hk
        by_cases hkn : k < n
        · exact hskip k hkn
        · have heq : k = n := by omega
          rw [heq, hn]
          exact hbc.1

end GroupApproximation.GGT.VanKampen.PermFirstReturn

#audit_axioms GroupApproximation.GGT.VanKampen.PermFirstReturn.sameCycle_iff
#audit_axioms GroupApproximation.GGT.VanKampen.PermFirstReturn.orbitEquiv
#audit_axioms GroupApproximation.GGT.VanKampen.PermFirstReturn.exists_pow_of_skip_walk
