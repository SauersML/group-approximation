import GroupApproximation.CharClass.ParityPWuTransport
import GroupApproximation.CharClass.ParityPWuCartanNarrow

/-!
# The field (W) from a split family, over narrowed reduced-power data

Lane `lx-splitK` (owner of `ParityP*`).

`ParityPWuTransport.wu_field_of_splitting` over `ParityP.PowerDataN`.  Two changes:

* the data are the narrowed ones (`PowerDataN`: `P⁰` on the roots and on `1`, Cartan for a root times
  a product of roots);
* the intertwining of the reduced powers is asked only at the classes the proof reads,
  `ρ (PH i (γ (i+1))) = D.P i (ρ (γ (i+1)))`.

The padding and evaluation lemmas of `ParityPWuTransport` are reused unchanged.

## Main results

* `ParityP.wu_isDecomposable_of_splittingN` — the diagonal Wu relation for the real Chern classes.
* `ParityP.wu_field_of_splittingN` — the field `wu` of `ParityPData`/`ParityPDataN`, in its exact
  shape, with `c i = m^i·wuCoeff p i`.
-/

set_option autoImplicit false

namespace GroupApproximation.CharClass

namespace ParityP

open MvPolynomial

section SplittingN

variable {H A σ : Type*} [CommRing H] [CommRing A] [DecidableEq σ]

/-- **The diagonal Wu relation, for a split family, from narrowed data.** -/
theorem wu_isDecomposable_of_splittingN {p : ℕ} (hp : 2 ≤ p) (D : PowerDataN σ A p)
    (ρ : H →+* A) (hρ : Function.Injective ρ) (γ : ℕ → H) (hγ : ∀ k, ρ (γ k) = D.gamma k)
    (PH : ℕ → H →+ H) (hP : ∀ i : ℕ, ρ (PH i (γ (i + 1))) = D.P i (ρ (γ (i + 1)))) (m : ℤ)
    (hκ : D.κ = (m : A)) (i : ℕ) :
    IsDecomposable γ (i * p + 1)
      (PH i (γ (i + 1)) - ((m ^ i * wuCoeff p i : ℤ) : H) * γ (i * p + 1)) := by
  obtain ⟨g, hge, hgw⟩ := exists_pad D.s D.y 0
  have hdec := isDecomposable_wuRHSP (n := D.s.card + 0) hp i
  have hlift : ∀ k, eval₂Hom (Int.castRingHom A) g (esymm (Fin (D.s.card + 0)) ℤ k)
      = ρ (γ k) := by
    intro k
    rw [hγ, D.gamma_def, eval₂Hom_esymm, hge]
  obtain ⟨w, hw, hψw⟩ := hdec.exists_lift (eval₂Hom (Int.castRingHom A) g) ρ hlift
  have hu : eval₂Hom (Int.castRingHom A) g
      (wuRHSP Finset.univ
          (fun l : Fin (D.s.card + 0) => (X l : MvPolynomial (Fin (D.s.card + 0)) ℤ) ^ p) X i
        - C (wuCoeff p i) * esymm (Fin (D.s.card + 0)) ℤ (i * p + 1))
      = wuRHSP D.s (fun l => D.y l ^ p) D.y i
        - ((wuCoeff p i : ℤ) : A) * D.gamma (i * p + 1) := by
    rw [map_sub, map_mul, eval₂Hom_wuRHSP, hgw p i (by omega), eval₂Hom_C, eq_intCast,
      eval₂Hom_esymm, hge, D.gamma_def]
  have hkey : ρ (PH i (γ (i + 1)) - ((m ^ i * wuCoeff p i : ℤ) : H) * γ (i * p + 1))
      = ρ (((m ^ i : ℤ) : H) * w) := by
    rw [map_mul ρ, map_intCast ρ, ← hψw, hu, map_sub, map_mul, map_intCast, hP i, hγ, hγ,
      D.p_gamma_succ_eq_smul i, hκ, Int.cast_mul, Int.cast_pow]
    ring
  rw [hρ hkey]
  exact hw.intCast_mul (m ^ i)

/-- **The field `wu`**, in its exact shape, from narrowed data. -/
theorem wu_field_of_splittingN {R : Type*} [CommRing R] {p : ℕ} (hp : 2 ≤ p) (ι : R →+* H)
    (D : PowerDataN σ A p) (ρ : H →+* A) (hρ : Function.Injective ρ) (γ : ℕ → H)
    (hγ : ∀ k, ρ (γ k) = D.gamma k) (PH : ℕ → H →+ H)
    (hP : ∀ i : ℕ, ρ (PH i (γ (i + 1))) = D.P i (ρ (γ (i + 1)))) (m : ℤ) (hκ : D.κ = (m : A))
    (i : ℕ) :
    IsDecomposable γ (i * p + 1)
      (PH i (γ (i + 1)) - ι ((m ^ i * wuCoeff p i : ℤ) : R) * γ (i * p + 1)) := by
  rw [map_intCast]
  exact wu_isDecomposable_of_splittingN hp D ρ hρ γ hγ PH hP m hκ i

end SplittingN

end ParityP

#audit_axioms ParityP.wu_isDecomposable_of_splittingN
#audit_axioms ParityP.wu_field_of_splittingN

end GroupApproximation.CharClass
