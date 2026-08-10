import NonsoficGroupsExist.Matching.FinitePartialBijection
import NonsoficGroupsExist.Sofic.Asymptotics

/-!
# Asymptotic partial bijections

The cluster construction uses sequences of partial bijections whose missing
source and target have negligible density.  Two such sequences represent the
same arrow exactly when their disagreement has negligible density.  This file
constructs that relation and proves directly that it is a setoid.
-/

namespace NonsoficGroupsExist

/-- A sequence of finite partial bijections with negligible missing source and
target, measured against one common nonnegative scale. -/
structure AsymptoticPartialBijection (N : ℕ → ℝ)
    (Y Z : ℕ → FiniteModel) where
  map : ∀ n, FinitePartialBijection (Y n) (Z n)
  source_negligible :
    Negligible N (fun n ↦ ((map n).sourceDefect : ℝ))
  target_negligible :
    Negligible N (fun n ↦ ((map n).targetDefect : ℝ))

namespace AsymptoticPartialBijection

variable {N : ℕ → ℝ} {Y Z : ℕ → FiniteModel}

/-- The sequence of full identity arrows. -/
def refl (N : ℕ → ℝ) (Y : ℕ → FiniteModel) :
    AsymptoticPartialBijection N Y Y where
  map := fun n ↦ FinitePartialBijection.refl (Y n)
  source_negligible := by
    apply Negligible.congr (N := N) Negligible.zero
    intro n
    change 0 = ((Fintype.card (Y n) - (Finset.univ : Finset (Y n)).card : ℕ) : ℝ)
    simp
  target_negligible := by
    apply Negligible.congr (N := N) Negligible.zero
    intro n
    change 0 = ((Fintype.card (Y n) - (Finset.univ : Finset (Y n)).card : ℕ) : ℝ)
    simp

/-- Restricted identity arrows form an asymptotic arrow exactly when the
missing subsets have negligible density. -/
def reflOn (s : ∀ n, Finset (Y n))
    (hmissing : Negligible N
      (fun n ↦ ((Fintype.card (Y n) - (s n).card : ℕ) : ℝ))) :
    AsymptoticPartialBijection N Y Y where
  map := fun n ↦ FinitePartialBijection.reflOn (s n)
  source_negligible := by
    apply Negligible.congr hmissing
    intro n
    rfl
  target_negligible := by
    apply Negligible.congr hmissing
    intro n
    rfl

/-- Two asymptotic partial bijections are near when the density of vertices
where they cannot be compared or disagree tends to zero. -/
def Near (a b : AsymptoticPartialBijection N Y Z) : Prop :=
  Negligible N (fun n ↦ ((a.map n).disagreement (b.map n) |>.card : ℝ))

theorem near_refl (a : AsymptoticPartialBijection N Y Z) : Near a a := by
  apply Negligible.congr a.source_negligible
  intro n
  exact_mod_cast (a.map n).card_disagreement_self.symm

theorem near_symm {a b : AsymptoticPartialBijection N Y Z}
    (h : Near a b) : Near b a := by
  apply Negligible.congr h
  intro n
  rw [(b.map n).disagreement_comm (a.map n)]

theorem near_trans (hN : ∀ n, 0 ≤ N n)
    {a b c : AsymptoticPartialBijection N Y Z}
    (hab : Near a b) (hbc : Near b c) : Near a c := by
  have hsum := Negligible.add hab hbc
  apply Negligible.mono_nonneg hN (fun _ ↦ by positivity) (fun n ↦ ?_) hsum
  exact_mod_cast
    FinitePartialBijection.card_disagreement_le (a.map n) (b.map n) (c.map n)

/-- Negligible disagreement is an actual equivalence relation on candidates
once the common normalizing scale is nonnegative. -/
def nearSetoid (hN : ∀ n, 0 ≤ N n) :
    Setoid (AsymptoticPartialBijection N Y Z) where
  r := Near
  iseqv := ⟨near_refl, near_symm, near_trans hN⟩

/-- Quotient arrows modulo negligible disagreement. -/
abbrev QuotientArrow (hN : ∀ n, 0 ≤ N n) :=
  Quotient (nearSetoid (Y := Y) (Z := Z) hN)

end AsymptoticPartialBijection
end NonsoficGroupsExist
