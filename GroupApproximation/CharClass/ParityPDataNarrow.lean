import GroupApproximation.CharClass.ParityPSlice
import GroupApproximation.Meta.AxiomGuard

/-!
# Step D mod `p`, uniform in the stage, from a narrowed passage through `z`

Lane `lx-splitK` (owner of `ParityP*`), ruling of `lx-design` 2026-09-12.

`ParityPData.pH_z_mul : PH i (z * ι r) = z * ι (PR i r)` holds for normalised operations with
`P⁰ z = z`.  The raw reduced powers give `P⁰ z = c·z` for a constant nobody computes.  The Step D
induction reads the field once, at `r = b (i+1)`, right after `PR i (b (i+1)) = 0`.  So
`ParityPDataN` asks only for `pH_z_mul_zero : PR i r = 0 → PH i (z * ι r) = 0`.
`ParityP.pH_z_mul_zero_of_cartan` produces it from the Cartan formula at `z · ι r`, `P^{>0} z = 0`
and naturality along `ι`, with no value of `P⁰ z`.

Every other field and every result is that of `ParityPData`.

## Main results

* `ParityPDataN` — the narrowed hypotheses.
* `ParityP.pH_z_mul_zero_of_cartan` — the narrowed field from Cartan and `P^{>0} z = 0`.
* `ParityPDataN.b_eq_zero`, `b_eq_zero_of_mod`, `gamma_eq_zero`, `gamma_rank_eq_zero`,
  `gamma_top_eq_zero_of_slice`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace GroupApproximation.CharClass

open ParityP

/-- **The hypotheses of the even side mod `p`, narrowed.**  As `ParityPData`, with `pH_z_mul`
replaced by `pH_z_mul_zero`. -/
structure ParityPDataN (p : ℕ) (R H : Type*) [CommRing R] [CommRing H] where
  /-- The prime is at least `2`. -/
  p_two_le : 2 ≤ p
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
  /-- **`P^i` kills `z · ι r` whenever it kills `r`.**  The only passage through `z` Step D uses. -/
  pH_z_mul_zero : ∀ (i : ℕ) (r : R), PR i r = 0 → PH i (z * ι r) = 0
  /-- The mod-`p` Chern classes. -/
  γ : ℕ → H
  /-- The `H^*(Y)`-component. -/
  a : ℕ → R
  /-- The `z H^*(Y)`-component, indexed by the total index. -/
  b : ℕ → R
  /-- The Künneth decomposition of the Chern classes. -/
  γ_eq : ∀ k : ℕ, γ k = ι (a k) + z * ι (b k)
  /-- **(A)** Frobenius support of the slice class. -/
  a_eq_zero : ∀ q : ℕ, ¬ p ∣ q → a q = 0
  /-- **(I)** Instability at the index the argument uses. -/
  pR_b_succ : ∀ i : ℕ, PR i (b (i + 1)) = 0
  /-- The leading coefficient of the diagonal Wu relation. -/
  c : ℕ → R
  /-- The leading coefficient is a unit. -/
  c_isUnit : ∀ i : ℕ, IsUnit (c i)
  /-- **(W)** The diagonal Wu relation. -/
  wu : ∀ i : ℕ, IsDecomposable γ (i * p + 1)
    (PH i (γ (i + 1)) - ι (c i) * γ (i * p + 1))

namespace ParityP

/-- **The narrowed field**, from the Cartan formula at `z · ι r`, `P^{>0} z = 0`, and naturality
along `ι`.  No value of `P⁰ z` is used. -/
theorem pH_z_mul_zero_of_cartan {R H : Type*} [CommRing R] [CommRing H] {ι : R →+* H} {z : H}
    {PH : ℕ → H →+ H} {PR : ℕ → R →+ R}
    (cartan : ∀ (i : ℕ) (r : R),
      PH i (z * ι r) = ∑ j ∈ Finset.range (i + 1), PH j z * PH (i - j) (ι r))
    (hz : ∀ i : ℕ, 0 < i → PH i z = 0)
    (hι : ∀ (i : ℕ) (r : R), PH i (ι r) = ι (PR i r)) (i : ℕ) (r : R) (hr : PR i r = 0) :
    PH i (z * ι r) = 0 := by
  rw [cartan i r,
    Finset.sum_eq_single 0
      (fun j _ hj => by rw [hz j (Nat.pos_of_ne_zero hj), zero_mul])
      (fun h => absurd (Finset.mem_range.mpr (Nat.succ_pos i)) h),
    Nat.sub_zero, hι, hr, map_zero, mul_zero]

end ParityP

namespace ParityPDataN

variable {p : ℕ} {R H : Type*} [CommRing R] [CommRing H] (D : ParityPDataN p R H)

/-- The Künneth decomposition of a product of Chern classes. -/
theorem gammaProd_eq (L : List ℕ) :
    gammaProd D.γ L = D.ι (aProd D.a L) + D.z * D.ι (bPart D.a D.b L) := by
  induction L with
  | nil =>
    simp only [gammaProd_nil, aProd_nil, bPart_nil, map_one, map_zero, mul_zero, add_zero]
  | cons α L ih =>
    have e : gammaProd D.γ (α :: L)
        = D.ι (D.a α) * D.ι (aProd D.a L)
          + D.z * (D.ι (D.b α) * D.ι (aProd D.a L) + D.ι (D.a α) * D.ι (bPart D.a D.b L))
          + D.z * D.z * (D.ι (D.b α) * D.ι (bPart D.a D.b L)) := by
      rw [gammaProd_cons, ih, D.γ_eq α]; ring
    rw [e, D.z_mul_z, zero_mul, add_zero]
    simp only [aProd_cons, bPart_cons, map_mul, map_add]

/-- The decomposables have no `z`-part, once every earlier `b` in the residue class vanishes. -/
theorem exists_iota_of_isDecomposable {N : ℕ}
    (hb : ∀ α c : ℕ, 1 ≤ c → α + c * p = N → D.b α = 0) :
    ∀ {u : H}, IsDecomposable D.γ N u → ∃ w : R, u = D.ι w := by
  intro u hu
  induction hu with
  | monomial L hpos hsum hlen =>
    refine ⟨aProd D.a L, ?_⟩
    rw [D.gammaProd_eq L,
      bPart_eq_zero D.a_eq_zero hb L hpos 0 (by simpa using hsum) (Or.inr hlen),
      map_zero, mul_zero, add_zero]
  | zero => exact ⟨0, (map_zero D.ι).symm⟩
  | add u v _hu _hv ihu ihv =>
    obtain ⟨w₁, h₁⟩ := ihu
    obtain ⟨w₂, h₂⟩ := ihv
    exact ⟨w₁ + w₂, by rw [h₁, h₂, map_add]⟩
  | neg u _hu ihu =>
    obtain ⟨w, h⟩ := ihu
    exact ⟨-w, by rw [h, map_neg]⟩

/-- **The inductive step.** -/
theorem b_step (i : ℕ) (ih : ∀ i' : ℕ, i' < i → D.b (i' * p + 1) = 0) :
    D.b (i * p + 1) = 0 := by
  have hb : ∀ α c : ℕ, 1 ≤ c → α + c * p = i * p + 1 → D.b α = 0 := by
    intro α c hc hα
    have hci : c ≤ i := by
      by_contra hcon
      have hcon' : i + 1 ≤ c := by omega
      have h1 : (i + 1) * p ≤ c * p := Nat.mul_le_mul hcon' (le_refl p)
      rw [add_mul, one_mul] at h1
      have h2 := D.p_two_le
      omega
    obtain ⟨i', hi'⟩ : ∃ i', i = i' + c := ⟨i - c, by omega⟩
    have hα' : α = i' * p + 1 := by
      rw [hi', add_mul] at hα
      omega
    rw [hα']
    exact ih i' (by omega)
  have hL : D.PH i (D.γ (i + 1)) = D.ι (D.PR i (D.a (i + 1))) := by
    rw [D.γ_eq (i + 1), map_add, D.pH_ι, D.pH_z_mul_zero i (D.b (i + 1)) (D.pR_b_succ i),
      add_zero]
  obtain ⟨w, hw⟩ := D.exists_iota_of_isDecomposable hb (D.wu i)
  have hw' : D.ι w = D.ι (D.PR i (D.a (i + 1)))
      - D.ι (D.c i) * (D.ι (D.a (i * p + 1)) + D.z * D.ι (D.b (i * p + 1))) := by
    rw [← hw, hL, D.γ_eq (i * p + 1)]
  have key : D.ι (D.PR i (D.a (i + 1)) - D.c i * D.a (i * p + 1) - w)
      + D.z * D.ι (-(D.c i * D.b (i * p + 1))) = 0 := by
    simp only [map_sub, map_mul, map_neg]
    rw [hw']
    ring
  have hcb : D.c i * D.b (i * p + 1) = 0 := neg_eq_zero.mp (D.z_inj _ _ key)
  exact (D.c_isUnit i).mul_right_eq_zero.mp hcb

/-- **Step D mod `p`, uniform in the stage.** -/
theorem b_eq_zero : ∀ i : ℕ, D.b (i * p + 1) = 0 := by
  suffices H' : ∀ M i : ℕ, i ≤ M → D.b (i * p + 1) = 0 by
    intro i
    exact H' i i le_rfl
  intro M
  induction M with
  | zero => exact fun i hi => D.b_step i fun i' hi' => absurd hi' (by omega)
  | succ M ihM => exact fun i hi => D.b_step i fun i' hi' => ihM i' (by omega)

/-- **Step D mod `p`**, in residue form. -/
theorem b_eq_zero_of_mod {N : ℕ} (hN : N % p = 1) : D.b N = 0 := by
  have h1 := D.b_eq_zero (N / p)
  have h3 := Nat.div_add_mod' N p
  rw [hN] at h3
  rwa [h3] at h1

/-- **The even side mod `p`.** -/
theorem gamma_eq_zero {r : ℕ} (hr : r % p = 1) (ha : D.a r = 0) : D.γ r = 0 := by
  rw [D.γ_eq r, ha, D.b_eq_zero_of_mod hr, map_zero, mul_zero, add_zero]

/-- **Step D mod `p`, in the tower's indexing.** -/
theorem gamma_rank_eq_zero {n m : ℕ} (hn : p ∣ n) (hm : p ∣ m)
    (ha : D.a (n + 1 + m) = 0) : D.γ (n + 1 + m) = 0 := by
  refine D.gamma_eq_zero ?_ ha
  obtain ⟨s, rfl⟩ := hn
  obtain ⟨t, rfl⟩ := hm
  have hrw : p * s + 1 + p * t = p * (s + t) + 1 := by ring
  rw [hrw, Nat.mul_add_mod, Nat.mod_eq_of_lt (by have := D.p_two_le; omega)]

/-- **Step D mod `p`, at the top index of a stage.** -/
theorem gamma_top_eq_zero_of_slice {n : ℕ} (hn : p ∣ n)
    {J : Type*} (u : Finset J) (gen : J → R) (d : J → ℕ) (hd : ∀ j ∈ u, p ∣ d j)
    (hslice : ∀ q : ℕ, D.a q = (sliceClass u gen d).coeff q) :
    D.γ (n + 1 + ∑ j ∈ u, d j) = 0 := by
  refine D.gamma_rank_eq_zero hn (Finset.dvd_sum hd) ?_
  rw [hslice]
  exact sliceClass_coeff_eq_zero_of_lt u gen d (by omega)

end ParityPDataN

#audit_axioms ParityPDataN
#audit_axioms ParityP.pH_z_mul_zero_of_cartan
#audit_axioms ParityPDataN.b_eq_zero
#audit_axioms ParityPDataN.gamma_rank_eq_zero
#audit_axioms ParityPDataN.gamma_top_eq_zero_of_slice

end GroupApproximation.CharClass
