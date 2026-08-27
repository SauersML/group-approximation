import Mathlib.Data.Fintype.Card

/-!
# A finite paired quotient cannot carry the binary Leavitt transports

The radical-quotient endpoint for the binary Leavitt atlas can be expressed
without choosing bases or mentioning the coefficient ring.  Suppose a
pairing between two finite types separates points on both sides.  If two
diagonal transport pairs preserve the pairing, then the first transport on
the left and the second transport on the right are bijections.  A crossed
transport which annihilates the pairing therefore makes the entire pairing
empty, contradicting nontriviality.

This is the exact finite endpoint of the paired-radical-quotient program.  It
does not construct those quotients from Hilbert--Schmidt microstates; that is
the remaining analytic extraction gate.
-/

namespace GroupApproximation

variable {V W : Type*} [Finite V] [Finite W]

/-- **Finite paired-quotient obstruction.**  A point-separating nonempty
pairing on two finite types cannot have two pairing-preserving diagonal
transports and one pairing-annihilating crossed transport.

For the binary Leavitt pairing `b(a,b) = ell (a*b)`, the maps are right
multiplication by `t_0,t_1` on the left radical quotient and left
multiplication by `s_0,s_1` on the right radical quotient. -/
theorem no_finite_nonempty_separating_pairing_with_leavitt_transports
    (pair : V → W → Prop)
    (R₀ R₁ : V → V) (L₀ L₁ : W → W)
    (hleft : ∀ {v v' : V}, (∀ w, pair v w ↔ pair v' w) → v = v')
    (hright : ∀ {w w' : W}, (∀ v, pair v w ↔ pair v w') → w = w')
    (h₀₀ : ∀ v w, pair (R₀ v) (L₀ w) ↔ pair v w)
    (h₁₁ : ∀ v w, pair (R₁ v) (L₁ w) ↔ pair v w)
    (h₀₁ : ∀ v w, ¬ pair (R₀ v) (L₁ w)) :
    ¬ ∃ v w, pair v w := by
  have hR₀inj : Function.Injective R₀ := by
    intro v v' hv
    apply hleft
    intro w
    rw [← h₀₀ v w, ← h₀₀ v' w, hv]
  have hL₁inj : Function.Injective L₁ := by
    intro w w' hw
    apply hright
    intro v
    rw [← h₁₁ v w, ← h₁₁ v w', hw]
  have hR₀surj : Function.Surjective R₀ :=
    Finite.surjective_of_injective hR₀inj
  have hL₁surj : Function.Surjective L₁ :=
    Finite.surjective_of_injective hL₁inj
  rintro ⟨v, w, hvw⟩
  obtain ⟨v₀, hv₀⟩ := hR₀surj v
  obtain ⟨w₁, hw₁⟩ := hL₁surj w
  apply h₀₁ v₀ w₁
  simpa only [hv₀, hw₁] using hvw

end GroupApproximation
