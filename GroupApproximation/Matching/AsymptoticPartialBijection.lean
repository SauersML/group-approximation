import GroupApproximation.Matching.FinitePartialBijection
import GroupApproximation.Sofic.Asymptotics

/-!
# Asymptotic partial bijections

The cluster construction uses sequences of partial bijections whose missing
source and target have negligible density.  Two such sequences represent the
same arrow exactly when their disagreement has negligible density.  This file
constructs that relation and proves directly that it is a setoid.
-/

namespace GroupApproximation

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

variable {N : ℕ → ℝ} {Y Z W V : ℕ → FiniteModel}

@[ext] theorem ext {a b : AsymptoticPartialBijection N Y Z}
    (hmap : a.map = b.map) : a = b := by
  cases a
  cases b
  cases hmap
  rfl

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

/-- Reverse every finite partial bijection in the sequence. -/
def symm (a : AsymptoticPartialBijection N Y Z) :
    AsymptoticPartialBijection N Z Y where
  map := fun n ↦ (a.map n).symm
  source_negligible := by
    simpa only [FinitePartialBijection.sourceDefect_symm] using
      a.target_negligible
  target_negligible := by
    simpa only [FinitePartialBijection.targetDefect_symm] using
      a.source_negligible

/-- Compose two asymptotic partial bijections.  The finite injectivity bound
proves that the new missing source and target remain negligible. -/
noncomputable def trans (hN : ∀ n, 0 ≤ N n)
    (a : AsymptoticPartialBijection N Y Z)
    (b : AsymptoticPartialBijection N Z W) :
    AsymptoticPartialBijection N Y W where
  map := fun n ↦ (a.map n).trans (b.map n)
  source_negligible := by
    apply Negligible.mono_nonneg hN (fun _ ↦ by positivity) (fun n ↦ ?_)
      (Negligible.add a.source_negligible b.source_negligible)
    exact_mod_cast (a.map n).sourceDefect_trans_le (b.map n)
  target_negligible := by
    apply Negligible.mono_nonneg hN (fun _ ↦ by positivity) (fun n ↦ ?_)
      (Negligible.add b.target_negligible a.target_negligible)
    exact_mod_cast (a.map n).targetDefect_trans_le (b.map n)

@[simp] theorem symm_symm (a : AsymptoticPartialBijection N Y Z) :
    a.symm.symm = a := by
  apply ext
  funext n
  exact (a.map n).symm_symm

@[simp] theorem refl_trans (hN : ∀ n, 0 ≤ N n)
    (a : AsymptoticPartialBijection N Y Z) :
    (refl N Y).trans hN a = a := by
  apply ext
  funext n
  exact (a.map n).refl_trans

@[simp] theorem trans_refl (hN : ∀ n, 0 ≤ N n)
    (a : AsymptoticPartialBijection N Y Z) :
    a.trans hN (refl N Z) = a := by
  apply ext
  funext n
  exact (a.map n).trans_refl

theorem trans_assoc (hN : ∀ n, 0 ≤ N n)
    (a : AsymptoticPartialBijection N Y Z)
    (b : AsymptoticPartialBijection N Z W)
    (c : AsymptoticPartialBijection N W V) :
    (a.trans hN b).trans hN c = a.trans hN (b.trans hN c) := by
  apply ext
  funext n
  exact (a.map n).trans_assoc (b.map n) (c.map n)

theorem symm_trans (hN : ∀ n, 0 ≤ N n)
    (a : AsymptoticPartialBijection N Y Z)
    (b : AsymptoticPartialBijection N Z W) :
    (a.trans hN b).symm = b.symm.trans hN a.symm := by
  apply ext
  funext n
  exact (a.map n).symm_trans (b.map n)

theorem trans_symm (hN : ∀ n, 0 ≤ N n)
    (a : AsymptoticPartialBijection N Y Z) :
    a.trans hN a.symm =
      reflOn (fun n ↦ (a.map n).source) a.source_negligible := by
  apply ext
  funext n
  exact (a.map n).trans_symm

theorem symm_trans_self (hN : ∀ n, 0 ≤ N n)
    (a : AsymptoticPartialBijection N Y Z) :
    a.symm.trans hN a =
      reflOn (fun n ↦ (a.map n).target) a.target_negligible := by
  apply ext
  funext n
  exact (a.map n).symm_trans_self

/-- Two asymptotic partial bijections are near when the density of vertices
where they cannot be compared or disagree tends to zero. -/
def Near (a b : AsymptoticPartialBijection N Y Z) : Prop :=
  Negligible N (fun n ↦ ((a.map n).twoSidedDisagreement (b.map n) : ℝ))

theorem near_refl (a : AsymptoticPartialBijection N Y Z) : Near a a := by
  apply Negligible.congr
    (Negligible.add a.source_negligible a.target_negligible)
  intro n
  exact_mod_cast (a.map n).twoSidedDisagreement_self.symm

theorem near_symm {a b : AsymptoticPartialBijection N Y Z}
    (h : Near a b) : Near b a := by
  apply Negligible.congr h
  intro n
  exact_mod_cast ((b.map n).twoSidedDisagreement_comm (a.map n)).symm

theorem near_trans (hN : ∀ n, 0 ≤ N n)
    {a b c : AsymptoticPartialBijection N Y Z}
    (hab : Near a b) (hbc : Near b c) : Near a c := by
  have hsum := Negligible.add hab hbc
  apply Negligible.mono_nonneg hN (fun _ ↦ by positivity) (fun n ↦ ?_) hsum
  exact_mod_cast FinitePartialBijection.twoSidedDisagreement_le
    (a.map n) (b.map n) (c.map n)

/-- Composition respects negligible disagreement in both arguments. -/
theorem trans_near_congr (hN : ∀ n, 0 ≤ N n)
    {a a' : AsymptoticPartialBijection N Y Z}
    {b b' : AsymptoticPartialBijection N Z W}
    (haa' : Near a a') (hbb' : Near b b') :
    Near (a.trans hN b) (a'.trans hN b') := by
  have hsum := Negligible.add haa' hbb'
  apply Negligible.mono_nonneg hN (fun _ ↦ by positivity) (fun n ↦ ?_) hsum
  exact_mod_cast FinitePartialBijection.twoSidedDisagreement_trans_le
    (a.map n) (a'.map n) (b.map n) (b'.map n)

/-- Reversal respects negligible disagreement definitionally because the
error is counted in both directions. -/
theorem symm_near_congr {a b : AsymptoticPartialBijection N Y Z}
    (h : Near a b) : Near a.symm b.symm := by
  apply Negligible.congr h
  intro n
  exact_mod_cast ((a.map n).twoSidedDisagreement_symm (b.map n)).symm

theorem reflOn_near_refl (s : ∀ n, Finset (Y n))
    (hmissing : Negligible N
      (fun n ↦ ((Fintype.card (Y n) - (s n).card : ℕ) : ℝ))) :
    Near (reflOn s hmissing) (refl N Y) := by
  have htwo := Negligible.const_mul 2 hmissing
  apply Negligible.congr htwo
  intro n
  exact_mod_cast
    (FinitePartialBijection.twoSidedDisagreement_reflOn_refl (s n)).symm

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
end GroupApproximation
