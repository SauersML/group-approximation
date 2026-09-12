import GroupApproximation.CharClass.ParityPWuTransport
import GroupApproximation.CharClass.ParityPSlice

/-!
# Step D mod `p` from the splitting principle: the record the real objects supply

Lane `lix-evenside` (successor of `sp-evenside`), program note §1.4, deliverable 2's interface.

`ParityPData` asks for the diagonal Wu relation (W) and a unit leading coefficient as fields.
The real objects do not supply them in that form.  They supply the Cartan formula, `P^0 = id`,
`P(z) = z`, instability, the slice class, and the splitting principle: an injective ring map
from the Chern classes into a ring carrying a split family of roots with `P(y) = y + κ·y^p`.
This file is the record in that form, `SplitStepDData`, together with the constructor
`SplitStepDData.toParityPData`, which derives every field of `ParityPData`, and the tower-facing
endpoint `SplitStepDData.gamma_top_eq_zero`.

What remains for the bridge to the real mapping torus is to fill this record from the
cohomology over `F_p`: the reduced powers with Cartan, `P^0 = id` and instability
(`lix-steenrod`); the Chern classes over `K` via Leray–Hirsch and the splitting principle
(`lix-lh`, `lix-coeff`); commutativity of the even part (`lix-cupone`); and Künneth
uniqueness for `z_inj`.

## Main results

* `ParityP.HasSplittingP` — the splitting principle at the prime `p`, with the extension hidden.
* `SplitStepDData` — the hypotheses of the even side as the real objects supply them.
* `SplitStepDData.toParityPData` — every field of `ParityPData`, including (W) and `c_isUnit`.
* `SplitStepDData.gamma_top_eq_zero` — `γ_{(∑_j d_j) + (n+1)}(W) = 0` for `p ∣ n` and
  `p ∣ d_j`, in the index order of the rank-generic `F₂` bridge.
-/

set_option autoImplicit false

universe u

namespace GroupApproximation.CharClass

open ParityP

/-- **The splitting principle at the prime `p`.**  The classes `γ` embed, by an injective ring
map `ρ`, into a ring `A` carrying a split family of roots whose elementary symmetric functions
are the images of `γ`, the reduced powers `PH` are intertwined with those of the roots, and the
normalisation constant is the integer `κ`. -/
def ParityP.HasSplittingP (p : ℕ) {H : Type u} [CommRing H] (γ : ℕ → H) (PH : ℕ → H →+ H)
    (κ : ℤ) : Prop :=
  ∃ (A : Type u) (_ : CommRing A) (σ : Type u) (_ : DecidableEq σ) (D : PowerData σ A p)
    (ρ : H →+* A), Function.Injective ρ ∧ (∀ k, ρ (γ k) = D.gamma k) ∧
      (∀ (i : ℕ) (x : H), ρ (PH i x) = D.P i (ρ x)) ∧ D.κ = (κ : A)

/-- **The even side mod `p`, as the real objects supply it.**  `R` is `H^*(Y; F_p)` and `H` the
even part of `H^*(N; F_p)`; `a k`, `b k` are the Künneth components of the `k`-th Chern class;
`w` is the weight of `z = t x`. -/
structure SplitStepDData (p : ℕ) (R H : Type u) [CommRing R] [CommRing H] where
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
  /-- `P^0 = id`. -/
  pH_zero : ∀ x : H, PH 0 x = x
  /-- The Cartan formula. -/
  cartan : ∀ (i : ℕ) (x y : H),
    PH i (x * y) = ∑ j ∈ Finset.range (i + 1), PH j x * PH (i - j) y
  /-- `P(z) = z`. -/
  pH_z : ∀ i : ℕ, 0 < i → PH i z = 0
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
  /-- `z` has weight at least two (`n ≥ 1`). -/
  two_le_w : 2 ≤ w
  /-- Instability for the `z`-components. -/
  instability : Instability PR b w
  /-- The normalisation constant of `P(h) = h + κ·h^p`, as an integer. -/
  κ : ℤ
  /-- The normalisation constant is a unit in the coefficients. -/
  κ_isUnit : IsUnit (κ : R)
  /-- The splitting principle. -/
  split : HasSplittingP p γ PH κ

namespace SplitStepDData

variable {p : ℕ} {R H : Type u} [CommRing R] [CommRing H]

/-- **Every field of `ParityPData`**, from the record and the slice class.  The leading
coefficient is `κ^i·wuCoeff p i`, a unit because `p = 0`; (W) is
`ParityP.wu_field_of_splitting`. -/
def toParityPData [ExpChar R p] (D : SplitStepDData p R H) {J : Type*} (u : Finset J)
    (gen : J → R) (d : J → ℕ) (hd : ∀ j ∈ u, p ∣ d j)
    (hslice : ∀ q : ℕ, D.a q = (sliceClass u gen d).coeff q) : ParityPData p R H where
  p_two_le := D.p_two_le
  ι := D.ι
  z := D.z
  z_mul_z := D.z_mul_z
  z_inj := D.z_inj
  PH := D.PH
  PR := D.PR
  pH_ι := D.pH_ι
  pH_z_mul := pH_z_mul_of_cartan D.pH_zero D.cartan D.pH_z D.pH_ι
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
    exact wu_field_of_splitting D.p_two_le D.ι P ρ hρ D.γ hγ D.PH hP D.κ hκ i

/-- **Step D mod `p`, from the splitting principle, uniform in the stage.**  If `p ∣ n` and
every `d_j` is divisible by `p`, the Chern class at the rank `(∑_j d_j) + (n + 1)` vanishes.
For the tower `d_j = n·2^j` both divisibilities come from `p ∣ n` alone. -/
theorem gamma_top_eq_zero [ExpChar R p] (D : SplitStepDData p R H) {n : ℕ} (hn : p ∣ n)
    {J : Type*} (u : Finset J) (gen : J → R) (d : J → ℕ) (hd : ∀ j ∈ u, p ∣ d j)
    (hslice : ∀ q : ℕ, D.a q = (sliceClass u gen d).coeff q) :
    D.γ ((∑ j ∈ u, d j) + (n + 1)) = 0 := by
  have h := (D.toParityPData u gen d hd hslice).gamma_top_eq_zero_of_slice hn u gen d hd hslice
  rw [Nat.add_comm (n + 1)] at h
  exact h

end SplitStepDData

end GroupApproximation.CharClass
