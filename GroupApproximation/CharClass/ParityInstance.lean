import GroupApproximation.CharClass.ParityEven
import GroupApproximation.CharClass.SteenrodTotal
import GroupApproximation.CharClass.CohomologyShapes

/-!
# Assembling `ParityData` for the LIX mapping torus

`ParityEven.lean` proves the even side of Lemma 2 over the abstract structure
`ParityData R H`.  This file instantiates `R` and `H` at the real objects — the
mod-2 cohomology rings `TotalH Y = ⨁_n H^n(Y; F₂)` and `TotalH N` of
`cc-projective`'s `ChernTotalRing` — and discharges every field that the topology
lanes have already landed, leaving the rest as **named hypotheses of one
theorem**, `parityData_of`.  Each peer landing turns exactly one hypothesis into
a lemma application, and the final instantiation of Lemma 2's even half is a
one-line use of `ParityData.gamma_top_eq_zero_of_slice`.

## What is discharged here, today

* `two_eq_zero` — `totalH_two_eq_zero`: `1 + 1 = 0` already in `H^0`.
* `ι` — `TotalH.map p`, pullback along the projection `p : N ⟶ Y`, a ring map.
* `t`, `x` — `tClass`, `xClass`: pullbacks of classes on the two sphere factors.
* `t_mul_t` — `mul_self_pull_sphere_eq_zero`: `t ⌣ t` is pulled back from
  `H²(S¹) = 0`.
* `sqH_t`, `sqH_x` — `sq_pull_sphere_eq_zero`: `Sq^k t` is pulled back from
  `H^{k+1}(S¹) = 0` for `k > 0`, and likewise for `x` from `H^{k+5}(S⁵) = 0`.
  Both are naturality (`Steenrod.SqH_map`) plus the sphere's vanishing, and
  neither needs instability or the Cartan formula.
* `SqH`, `SqR` — `Steenrod.SqH N`, `Steenrod.SqH Y`.
* `sqH_zero_apply` — `Steenrod.SqH_zero_apply`.
* `sqH_ι` — `Steenrod.SqH_map`, on the nose.

## What is left as a hypothesis

Seven, listed with their owners in `notes/lix-lane-reports/cc-wu.md` §7.  Two
helpers are provided so that two of them become mechanical once the underlying
statement lands: `sq_b_of_grading` turns "`b k` sits in degree `2k − 6`" into the
`sq_b` field, and `ParityData.gamma_top_eq_zero_of_slice` (in `ParityEven.lean`)
turns the slice class into `a_zero`, `a_odd` and the top vanishing.

Nothing in this file mentions the rank of the bundle: the parity statement is
rank-free.
-/

set_option autoImplicit false

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation
namespace CharClass
namespace Wu

noncomputable section

/-! ## 1. Characteristic two in `TotalH` -/

/-- Mod-2 cohomology is killed by two in every degree. -/
theorem hmod2_add_self {X : TopCat.{0}} {n : ℕ} (a : Hmod2 X n) : a + a = 0 := by
  have h : (2 : ZMod 2) • a = 0 := by
    rw [show (2 : ZMod 2) = 0 from by decide, zero_smul]
  rwa [two_smul] at h

/-- **`cc-wu`'s `two_eq_zero` field.** -/
theorem totalH_two_eq_zero (X : TopCat.{0}) : (2 : TotalH X) = 0 := by
  rw [← one_add_one_eq_two, ← TotalH.of_one X, ← map_add, hmod2_add_self, map_zero]

/-! ## 2. Classes pulled back from a sphere factor -/

variable {N Y S₁ S₅ : TopCat.{0}}

/-- The degree-one class of `H^*(N)` pulled back from the circle factor. -/
def tClass (q₁ : N ⟶ S₁) (σ₁ : Hmod2 S₁ 1) : TotalH N :=
  TotalH.map q₁ (TotalH.of S₁ 1 σ₁)

/-- The degree-five class of `H^*(N)` pulled back from the `S⁵` factor. -/
def xClass (q₅ : N ⟶ S₅) (σ₅ : Hmod2 S₅ 5) : TotalH N :=
  TotalH.map q₅ (TotalH.of S₅ 5 σ₅)

/-- **A positive square of a class pulled back from a sphere vanishes**, because
it is pulled back from a degree in which the sphere has no cohomology.  This is
`cc-wu`'s `sqH_t` and `sqH_x`; it uses naturality only, not instability and not
the Cartan formula. -/
theorem sq_pull_sphere_eq_zero {S : TopCat.{0}} (q : N ⟶ S) {m : ℕ}
    (hS : HasSphereCohomology S m) (σ : Hmod2 S m) {k : ℕ} (hk : 0 < k) :
    Steenrod.SqH N k (TotalH.map q (TotalH.of S m σ)) = 0 := by
  rw [Steenrod.SqH_map, Steenrod.SqH_of]
  have hz : Sq k σ = 0 := hS.2.2 (k + m) (by omega) (by omega) (Sq k σ)
  rw [hz, map_zero, map_zero]

/-- **The cup square of a class pulled back from a sphere vanishes.**  This is
`cc-wu`'s `t_mul_t`. -/
theorem mul_self_pull_sphere_eq_zero {S : TopCat.{0}} (q : N ⟶ S) {m : ℕ}
    (hS : HasSphereCohomology S m) (σ : Hmod2 S m) (hm : 1 ≤ m) :
    TotalH.map q (TotalH.of S m σ) * TotalH.map q (TotalH.of S m σ) = 0 := by
  rw [← map_mul, ← TotalH.of_mul]
  have hz : cup σ σ = 0 := hS.2.2 (m + m) (by omega) (by omega) (cup σ σ)
  rw [hz, map_zero, map_zero]

/-! ## 3. Instability for the `t x`-components -/

/-- **`cc-wu`'s `sq_b` field from the grading.**  If `b k` vanishes for `k < 3`
and is concentrated in degree `2k − 6` otherwise, then instability
(`Steenrod.SqH_of_eq_zero_of_lt`) discharges `sq_b`.  For `k < 3` the field says
`b k = 0`, which is what the Künneth decomposition gives: `t x` already carries
degree six, so there is no room below the total index three. -/
theorem sq_b_of_grading (b : ℕ → TotalH Y)
    (hlow : ∀ k : ℕ, k < 3 → b k = 0)
    (hdeg : ∀ k c : ℕ, 2 * k = c + 6 → ∃ β : Hmod2 Y c, b k = TotalH.of Y c β) :
    ∀ k j : ℕ, 2 * k < j + 6 → Steenrod.SqH Y j (b k) = 0 := by
  intro k j hkj
  rcases Nat.lt_or_ge k 3 with hk | hk
  · rw [hlow k hk, map_zero]
  · obtain ⟨β, hβ⟩ := hdeg k (2 * k - 6) (by omega)
    rw [hβ]
    exact Steenrod.SqH_of_eq_zero_of_lt Y j (2 * k - 6) (by omega) β

/-! ## 4. The assembly -/

/-- **The `ParityData` of the LIX mapping torus.**

`N` is the mapping torus base `S¹ × S⁵ × Y`, `Y = ∏_j ℂP^{d_j}`, `p` the
projection to `Y`, and `q₁`, `q₅` the projections to the two sphere factors.
Every field that the landed layers supply is proved here; the seven remaining
inputs are the explicit hypotheses, one per field.  Their owners:

* `hcartan` — `cc-cartan` (the Cartan formula, transported to `Steenrod.SqH`
  on `TotalH N` by `cc-steenrod`);
* `htx_inj` — `cc-cohom-api` (Künneth for the two sphere factors);
* `hγ` — `cc-cohom-api` + `cc-projective` (the Künneth decomposition of the
  mod-2 Chern classes of `W`);
* `ha_zero`, `ha_odd` — `cc-projective` (the slice restriction; the slice class
  `∏_j (1 + h_j)^{d_j}` with each `d_j` even, then
  `sliceClass_coeff_zero` and `sliceClass_coeff_odd_eq_zero` of
  `ParityEvenSlice.lean`);
* `hsq_b` — `cc-cohom-api` (the degree of the `t x`-component), through
  `sq_b_of_grading`;
* `hwu` — `cc-projective` (the splitting principle), through
  `SqData.wu_diagonal` of `WuDiagonal.lean`. -/
def parityData_of
    (p : N ⟶ Y) (q₁ : N ⟶ S₁) (q₅ : N ⟶ S₅)
    (hS₁ : HasSphereCohomology S₁ 1) (hS₅ : HasSphereCohomology S₅ 5)
    (σ₁ : Hmod2 S₁ 1) (σ₅ : Hmod2 S₅ 5)
    (γ : ℕ → TotalH N) (a b : ℕ → TotalH Y)
    (hcartan : ∀ (n : ℕ) (u v : TotalH N),
      Steenrod.SqH N n (u * v)
        = ∑ i ∈ Finset.range (n + 1), Steenrod.SqH N i u * Steenrod.SqH N (n - i) v)
    (htx_inj : ∀ u v : TotalH Y,
      TotalH.map p u + tClass q₁ σ₁ * xClass q₅ σ₅ * TotalH.map p v = 0 → v = 0)
    (hγ : ∀ k : ℕ,
      γ k = TotalH.map p (a k) + tClass q₁ σ₁ * xClass q₅ σ₅ * TotalH.map p (b k))
    (ha_zero : a 0 = 1)
    (ha_odd : ∀ q : ℕ, Odd q → a q = 0)
    (hsq_b : ∀ k j : ℕ, 2 * k < j + 6 → Steenrod.SqH Y j (b k) = 0)
    (hwu : ∀ i : ℕ, Steenrod.SqH N (2 * i) (γ (i + 1))
      = ∑ j ∈ Finset.range (i + 1), γ (i - j) * γ (i + 1 + j)) :
    ParityData (TotalH Y) (TotalH N) where
  two_eq_zero := totalH_two_eq_zero Y
  ι := TotalH.map p
  t := tClass q₁ σ₁
  x := xClass q₅ σ₅
  t_mul_t := mul_self_pull_sphere_eq_zero q₁ hS₁ σ₁ (by omega)
  tx_inj := htx_inj
  SqH := Steenrod.SqH N
  SqR := Steenrod.SqH Y
  sqH_zero_apply := Steenrod.SqH_zero_apply N
  cartanH := hcartan
  sqH_t := fun n hn => sq_pull_sphere_eq_zero q₁ hS₁ σ₁ hn
  sqH_x := fun n hn => sq_pull_sphere_eq_zero q₅ hS₅ σ₅ hn
  sqH_ι := fun n r => Steenrod.SqH_map p n r
  γ := γ
  a := a
  b := b
  γ_eq := hγ
  a_zero := ha_zero
  a_odd := ha_odd
  sq_b := hsq_b
  wu := hwu

@[simp] theorem parityData_of_gamma
    (p : N ⟶ Y) (q₁ : N ⟶ S₁) (q₅ : N ⟶ S₅)
    (hS₁ : HasSphereCohomology S₁ 1) (hS₅ : HasSphereCohomology S₅ 5)
    (σ₁ : Hmod2 S₁ 1) (σ₅ : Hmod2 S₅ 5)
    (γ : ℕ → TotalH N) (a b : ℕ → TotalH Y)
    (hcartan : ∀ (n : ℕ) (u v : TotalH N),
      Steenrod.SqH N n (u * v)
        = ∑ i ∈ Finset.range (n + 1), Steenrod.SqH N i u * Steenrod.SqH N (n - i) v)
    (htx_inj : ∀ u v : TotalH Y,
      TotalH.map p u + tClass q₁ σ₁ * xClass q₅ σ₅ * TotalH.map p v = 0 → v = 0)
    (hγ : ∀ k : ℕ,
      γ k = TotalH.map p (a k) + tClass q₁ σ₁ * xClass q₅ σ₅ * TotalH.map p (b k))
    (ha_zero : a 0 = 1) (ha_odd : ∀ q : ℕ, Odd q → a q = 0)
    (hsq_b : ∀ k j : ℕ, 2 * k < j + 6 → Steenrod.SqH Y j (b k) = 0)
    (hwu : ∀ i : ℕ, Steenrod.SqH N (2 * i) (γ (i + 1))
      = ∑ j ∈ Finset.range (i + 1), γ (i - j) * γ (i + 1 + j)) (k : ℕ) :
    (parityData_of p q₁ q₅ hS₁ hS₅ σ₁ σ₅ γ a b hcartan htx_inj hγ ha_zero ha_odd
      hsq_b hwu).γ k = γ k := rfl

/-- **`a_zero` and `a_odd` from the slice class.**  Both `a`-hypotheses of
`parityData_of` are consequences of the single statement that `a` is the
coefficient sequence of `∏_j (1 + h_j)^{d_j}` with every `d_j` even. -/
theorem a_zero_of_slice (a : ℕ → TotalH Y) {J : Type} (u : Finset J) (h : J → TotalH Y)
    (d : J → ℕ) (hslice : ∀ q : ℕ, a q = (sliceClass u h d).coeff q) : a 0 = 1 := by
  rw [hslice 0, sliceClass_coeff_zero]

theorem a_odd_of_slice (a : ℕ → TotalH Y) {J : Type} (u : Finset J) (h : J → TotalH Y)
    (d : J → ℕ) (hd : ∀ j ∈ u, Even (d j))
    (hslice : ∀ q : ℕ, a q = (sliceClass u h d).coeff q) :
    ∀ q : ℕ, Odd q → a q = 0 := by
  intro q hq
  rw [hslice q]
  exact sliceClass_coeff_odd_eq_zero (totalH_two_eq_zero Y) u h d hd hq

/-- **Lemma 2, the even half, at the real objects.**  Under five hypotheses of
`parityData_of` — `ha_zero` and `ha_odd` are *not* among them, being consequences
of the slice class — and the slice class `∏_j (1 + h_j)^{d_j}` with every `d_j`
even, the top mod-2 Chern class of `W` vanishes in `H^*(N; F₂)`:
`γ_r(W) = 0` for `r = (∑_j d_j) + 3`.  Rank-free. -/
theorem gamma_top_eq_zero_of_slice_totalH
    (p : N ⟶ Y) (q₁ : N ⟶ S₁) (q₅ : N ⟶ S₅)
    (hS₁ : HasSphereCohomology S₁ 1) (hS₅ : HasSphereCohomology S₅ 5)
    (σ₁ : Hmod2 S₁ 1) (σ₅ : Hmod2 S₅ 5)
    (γ : ℕ → TotalH N) (a b : ℕ → TotalH Y)
    (hcartan : ∀ (n : ℕ) (u v : TotalH N),
      Steenrod.SqH N n (u * v)
        = ∑ i ∈ Finset.range (n + 1), Steenrod.SqH N i u * Steenrod.SqH N (n - i) v)
    (htx_inj : ∀ u v : TotalH Y,
      TotalH.map p u + tClass q₁ σ₁ * xClass q₅ σ₅ * TotalH.map p v = 0 → v = 0)
    (hγ : ∀ k : ℕ,
      γ k = TotalH.map p (a k) + tClass q₁ σ₁ * xClass q₅ σ₅ * TotalH.map p (b k))
    (hsq_b : ∀ k j : ℕ, 2 * k < j + 6 → Steenrod.SqH Y j (b k) = 0)
    (hwu : ∀ i : ℕ, Steenrod.SqH N (2 * i) (γ (i + 1))
      = ∑ j ∈ Finset.range (i + 1), γ (i - j) * γ (i + 1 + j))
    {J : Type} (u : Finset J) (h : J → TotalH Y) (d : J → ℕ)
    (hd : ∀ j ∈ u, Even (d j))
    (hslice : ∀ q : ℕ, a q = (sliceClass u h d).coeff q) :
    γ ((∑ j ∈ u, d j) + 3) = 0 :=
  (parityData_of p q₁ q₅ hS₁ hS₅ σ₁ σ₅ γ a b hcartan htx_inj hγ
    (a_zero_of_slice a u h d hslice) (a_odd_of_slice a u h d hd hslice)
    hsq_b hwu).gamma_top_eq_zero_of_slice u h d hd hslice

end

end Wu
end CharClass
end GroupApproximation
