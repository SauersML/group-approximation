import GroupApproximation.CharClass.ParityPSplitStepD
import GroupApproximation.CharClass.ParityPWuTransportNarrow
import GroupApproximation.CharClass.ParityPDataNarrow

/-!
# Step D mod `p` from the splitting principle, narrowed

Lane `lx-splitK` (owner of `ParityP*`), ruling of `lx-design` 2026-09-12.

`ParityPSplitStepD` over the narrowed data.

* `ParityP.HasSplittingPN` is `HasSplittingP` over `ParityP.PowerDataN`.  The intertwining of the
  reduced powers is asked only at the classes `γ (i+1)`.
* `SplitStepDDataN` is `SplitStepDData` with `pH_zero`, `cartan` and `pH_z` replaced by the single
  field `pH_z_mul_zero` (`ParityPDataN`), and `split : HasSplittingPN`.

## Main results

* `ParityP.HasSplittingPN`, `ParityP.HasSplittingPN.elim`.
* `SplitStepDDataN`, `SplitStepDDataN.toParityPDataN`, `SplitStepDDataN.gamma_top_eq_zero`.
-/

set_option autoImplicit false

universe u

namespace GroupApproximation.CharClass

open ParityP

/-- **The splitting principle at the prime `p`, narrowed.** -/
def ParityP.HasSplittingPN (p : ℕ) {H : Type u} [CommRing H] (γ : ℕ → H) (PH : ℕ → H →+ H)
    (κ : ℤ) : Prop :=
  ∃ (A : Type u) (_ : CommRing A) (σ : Type u) (_ : DecidableEq σ) (D : PowerDataN σ A p)
    (ρ : H →+* A), Function.Injective ρ ∧ (∀ k, ρ (γ k) = D.gamma k) ∧
      (∀ i : ℕ, ρ (PH i (γ (i + 1))) = D.P i (ρ (γ (i + 1)))) ∧ D.κ = (κ : A)

/-- **Destructuring `HasSplittingPN`.** -/
theorem ParityP.HasSplittingPN.elim {p : ℕ} {H : Type} [CommRing H] {γ : ℕ → H}
    {PH : ℕ → H →+ H} {κ : ℤ} (h : HasSplittingPN p γ PH κ) {C : Prop}
    (hC : ∀ (A : Type) [CommRing A] (σ : Type) [DecidableEq σ] (D : PowerDataN σ A p)
      (ρ : H →+* A), Function.Injective ρ → (∀ k, ρ (γ k) = D.gamma k) →
        (∀ i : ℕ, ρ (PH i (γ (i + 1))) = D.P i (ρ (γ (i + 1)))) → D.κ = (κ : A) → C) : C := by
  obtain ⟨A, _, σ, _, D, ρ, h1, h2, h3, h4⟩ := h
  exact hC A σ D ρ h1 h2 h3 h4

/-- **The even side mod `p`, as the real objects supply it, narrowed.** -/
structure SplitStepDDataN (p : ℕ) (R H : Type u) [CommRing R] [CommRing H] where
  /-- The prime is at least `2`. -/
  p_two_le : 2 ≤ p
  /-- `p = 0` in the coefficients. -/
  p_eq_zero : (p : R) = 0
  /-- The Künneth inclusion `H^*(Y) → H^*(N)`. -/
  ι : R →+* H
  /-- The class `z = t x`. -/
  z : H
  /-- `z² = 0`. -/
  z_mul_z : z * z = 0
  /-- Künneth uniqueness of the `z`-component. -/
  z_inj : ∀ u v : R, ι u + z * ι v = 0 → v = 0
  /-- The reduced powers on the even part of `H^*(N)`. -/
  PH : ℕ → H →+ H
  /-- The reduced powers on `H^*(Y)`. -/
  PR : ℕ → R →+ R
  /-- The reduced powers preserve the Künneth inclusion. -/
  pH_ι : ∀ (i : ℕ) (r : R), PH i (ι r) = ι (PR i r)
  /-- `P^i` kills `z · ι r` whenever it kills `r`. -/
  pH_z_mul_zero : ∀ (i : ℕ) (r : R), PR i r = 0 → PH i (z * ι r) = 0
  /-- The mod-`p` Chern classes. -/
  γ : ℕ → H
  /-- The `H^*(Y)`-component. -/
  a : ℕ → R
  /-- The `z H^*(Y)`-component, indexed by the total index. -/
  b : ℕ → R
  /-- The Künneth decomposition of the Chern classes. -/
  γ_eq : ∀ k : ℕ, γ k = ι (a k) + z * ι (b k)
  /-- The weight of `z`. -/
  w : ℕ
  /-- `z` has weight at least two. -/
  two_le_w : 2 ≤ w
  /-- Instability for the `z`-components. -/
  instability : Instability PR b w
  /-- The normalisation constant, as an integer. -/
  κ : ℤ
  /-- The normalisation constant is a unit in the coefficients. -/
  κ_isUnit : IsUnit (κ : R)
  /-- The splitting principle, narrowed. -/
  split : HasSplittingPN p γ PH κ

namespace SplitStepDDataN

variable {p : ℕ} {R H : Type u} [CommRing R] [CommRing H]

/-- **Every field of `ParityPDataN`**, from the record and the slice class. -/
def toParityPDataN [ExpChar R p] (D : SplitStepDDataN p R H) {J : Type*} (u : Finset J)
    (gen : J → R) (d : J → ℕ) (hd : ∀ j ∈ u, p ∣ d j)
    (hslice : ∀ q : ℕ, D.a q = (sliceClass u gen d).coeff q) : ParityPDataN p R H where
  p_two_le := D.p_two_le
  ι := D.ι
  z := D.z
  z_mul_z := D.z_mul_z
  z_inj := D.z_inj
  PH := D.PH
  PR := D.PR
  pH_ι := D.pH_ι
  pH_z_mul_zero := D.pH_z_mul_zero
  γ := D.γ
  a := D.a
  b := D.b
  γ_eq := D.γ_eq
  a_eq_zero := fun q hq => by
    rw [hslice]
    exact sliceClass_coeff_eq_zero_of_not_dvd p (by have := D.p_two_le; omega) u gen d hd hq
  pR_b_succ := pR_b_succ_of_instability D.two_le_w D.instability
  c := fun i => ((D.κ ^ i * wuCoeff p i : ℤ) : R)
  c_isUnit := fun i => isUnit_wuLeading D.p_eq_zero D.κ_isUnit i
  wu := fun i => by
    obtain ⟨A, _, σ, _, P, ρ, hρ, hγ, hP, hκ⟩ := D.split
    exact wu_field_of_splittingN D.p_two_le D.ι P ρ hρ D.γ hγ D.PH hP D.κ hκ i

/-- **Step D mod `p`, from the narrowed splitting principle, uniform in the stage.** -/
theorem gamma_top_eq_zero [ExpChar R p] (D : SplitStepDDataN p R H) {n : ℕ} (hn : p ∣ n)
    {J : Type*} (u : Finset J) (gen : J → R) (d : J → ℕ) (hd : ∀ j ∈ u, p ∣ d j)
    (hslice : ∀ q : ℕ, D.a q = (sliceClass u gen d).coeff q) :
    D.γ ((∑ j ∈ u, d j) + (n + 1)) = 0 := by
  have h := (D.toParityPDataN u gen d hd hslice).gamma_top_eq_zero_of_slice hn u gen d hd hslice
  rw [Nat.add_comm (n + 1)] at h
  exact h

end SplitStepDDataN

#audit_axioms ParityP.HasSplittingPN
#audit_axioms ParityP.HasSplittingPN.elim
#audit_axioms SplitStepDDataN
#audit_axioms SplitStepDDataN.toParityPDataN
#audit_axioms SplitStepDDataN.gamma_top_eq_zero

end GroupApproximation.CharClass
