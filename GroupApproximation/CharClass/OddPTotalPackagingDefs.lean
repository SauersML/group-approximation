import GroupApproximation.CharClass.OddPTotalGrading

/-!
# Packaging the reduced powers, part 1: the operations

From `OddPTotal.TotalReducedPowers p`: the inverse `μinv` of the degree-two constant, the
components of the total power `ptotOf`, the normalised graded operation
`totalP X i = Σ_d μ^{-(d/2 − i)}·projDeg_{d + 2i(p−1)} ∘ ptotOf_d` on the whole ring, and the total
power `totalPtot X` on the whole ring, both killing odd pieces and preserving evenness.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace OddPTotal

open CategoryTheory

noncomputable section

namespace TotalReducedPowers

variable {p : ℕ} (R : TotalReducedPowers p)

/-- The inverse of the `P⁰` constant in degree two. -/
def μinv : ZMod p := ((R.μ_isUnit.unit⁻¹ : (ZMod p)ˣ) : ZMod p)

theorem μinv_mul : R.μinv * R.μ = 1 := R.μ_isUnit.val_inv_mul

theorem μinv_pow_mul_pow (k : ℕ) : R.μinv ^ k * R.μ ^ k = 1 := by
  rw [← mul_pow, R.μinv_mul, one_pow]

/-- The total power, as an explicit sum. -/
theorem ptotOf_apply (X : TopCat.{0}) (q : ℕ) (x : Hmod (ZMod p) X q) :
    ptotOf R.D X q x = ∑ j ∈ Finset.range (p * q + 1),
      if j % 2 = 0 then TotalHOf.of (ZMod p) X (p * q - j) (R.D X q j x) else 0 := by
  rw [ptotOf, AddMonoidHom.finset_sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : j % 2 = 0
  · rw [if_pos hj, if_pos hj]; rfl
  · rw [if_neg hj, if_neg hj]; rfl

/-- **The components of the total power**: in degree `e ≤ pq` with `pq − e` even it is
`[D_{pq − e} x]`, and zero otherwise. -/
theorem component_ptotOf (X : TopCat.{0}) (q e : ℕ) (x : Hmod (ZMod p) X q) :
    TotalHOf.component (ZMod p) X e (ptotOf R.D X q x)
      = if h : e ≤ p * q ∧ (p * q - e) % 2 = 0 then
          cohCast (show p * q - (p * q - e) = e by omega) (R.D X q (p * q - e) x)
        else 0 := by
  rw [R.ptotOf_apply, map_sum]
  have hterm : ∀ j ∈ Finset.range (p * q + 1),
      TotalHOf.component (ZMod p) X e
          (if j % 2 = 0 then TotalHOf.of (ZMod p) X (p * q - j) (R.D X q j x) else 0)
        = if h : j % 2 = 0 ∧ p * q - j = e then cohCast h.2 (R.D X q j x) else 0 := by
    intro j _
    by_cases h1 : j % 2 = 0
    · rw [if_pos h1, component_of_eq_dite]
      by_cases h2 : p * q - j = e
      · rw [dif_pos h2, dif_pos ⟨h1, h2⟩]
      · rw [dif_neg h2, dif_neg (fun h => h2 h.2)]
    · rw [if_neg h1, map_zero, dif_neg (fun h => h1 h.1)]
  rw [Finset.sum_congr rfl hterm]
  by_cases h : e ≤ p * q ∧ (p * q - e) % 2 = 0
  · rw [dif_pos h, Finset.sum_eq_single (p * q - e)]
    · rw [dif_pos ⟨h.2, by omega⟩]
    · intro j hj hne
      refine dif_neg fun hc => hne ?_
      rw [Finset.mem_range] at hj
      obtain ⟨_, hc2⟩ := hc
      omega
    · intro hn
      exact absurd (Finset.mem_range.mpr (by omega)) hn
  · rw [dif_neg h]
    refine Finset.sum_eq_zero fun j hj => dif_neg fun hc => h ?_
    rw [Finset.mem_range] at hj
    obtain ⟨hc1, hc2⟩ := hc
    refine ⟨by omega, ?_⟩
    rw [show p * q - e = j by omega]
    exact hc1

/-- The total power vanishes above degree `pq`. -/
theorem component_ptotOf_of_lt (X : TopCat.{0}) (q e : ℕ) (x : Hmod (ZMod p) X q)
    (he : p * q < e) : TotalHOf.component (ZMod p) X e (ptotOf R.D X q x) = 0 := by
  rw [R.component_ptotOf, dif_neg (fun h => by omega)]

/-- The total power of a class of even degree vanishes in odd degrees. -/
theorem component_ptotOf_of_odd (X : TopCat.{0}) {q : ℕ} (hq : q % 2 = 0) (e : ℕ)
    (x : Hmod (ZMod p) X q) (he : e % 2 = 1) :
    TotalHOf.component (ZMod p) X e (ptotOf R.D X q x) = 0 := by
  rw [R.component_ptotOf, dif_neg]
  rintro ⟨hle, hev⟩
  have hpq : (p * q) % 2 = 0 := by rw [Nat.mul_mod, hq, mul_zero, Nat.zero_mod]
  omega

theorem ptotOf_isEven (X : TopCat.{0}) {q : ℕ} (hq : q % 2 = 0) (x : Hmod (ZMod p) X q) :
    TotalHOf.IsEven (ptotOf R.D X q x) := by
  intro e he
  exact R.component_ptotOf_of_odd X hq e x (Nat.odd_iff.mp he)

/-- Naturality of the total power. -/
theorem ptotOf_natural {X Y : TopCat.{0}} (f : X ⟶ Y) (q : ℕ) (x : Hmod (ZMod p) Y q) :
    ptotOf R.D X q (pull f q x) = TotalHOf.map (ZMod p) f (ptotOf R.D Y q x) := by
  rw [R.ptotOf_apply, R.ptotOf_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : j % 2 = 0
  · rw [if_pos hj, if_pos hj, TotalHOf.map_of, R.natural]
  · rw [if_neg hj, if_neg hj, map_zero]

/-! ## The graded operation -/

/-- The normalised reduced power `P^i` on one degree. -/
def pieceP (X : TopCat.{0}) (i d : ℕ) : TotalPieceOf (ZMod p) X d →+ TotalHOf (ZMod p) X :=
  if d % 2 = 0 ∧ 2 * i ≤ d then
    R.μinv ^ (d / 2 - i) • (projDeg (ZMod p) X (d + 2 * i * (p - 1))).comp (ptotOf R.D X d)
  else 0

theorem pieceP_apply (X : TopCat.{0}) (i d : ℕ) (c : TotalPieceOf (ZMod p) X d) :
    R.pieceP X i d c = if d % 2 = 0 ∧ 2 * i ≤ d then
      R.μinv ^ (d / 2 - i) • projDeg (ZMod p) X (d + 2 * i * (p - 1)) (ptotOf R.D X d c)
    else 0 := by
  rw [pieceP]
  by_cases h : d % 2 = 0 ∧ 2 * i ≤ d
  · rw [if_pos h, if_pos h]; rfl
  · rw [if_neg h, if_neg h]; rfl

/-- The normalised reduced power `P^i` on the whole cohomology ring. -/
def totalP (X : TopCat.{0}) (i : ℕ) : TotalHOf (ZMod p) X →+ TotalHOf (ZMod p) X :=
  DirectSum.toAddMonoid fun d => R.pieceP X i d

theorem totalP_of (X : TopCat.{0}) (i d : ℕ) (c : TotalPieceOf (ZMod p) X d) :
    R.totalP X i (TotalHOf.of (ZMod p) X d c) = R.pieceP X i d c :=
  DirectSum.toAddMonoid_of _ _ _

theorem pieceP_isEven (X : TopCat.{0}) (i d : ℕ) (c : TotalPieceOf (ZMod p) X d) :
    TotalHOf.IsEven (R.pieceP X i d c) := by
  rw [R.pieceP_apply]
  by_cases h : d % 2 = 0 ∧ 2 * i ≤ d
  · rw [if_pos h, projDeg_apply]
    refine isEven_smul (ZMod p) X _ (TotalHOf.isEven_of (ZMod p) X ?_ _)
    rw [Nat.even_iff]
    have : (2 * i * (p - 1)) % 2 = 0 := by rw [mul_assoc, Nat.mul_mod_right]
    omega
  · rw [if_neg h]
    exact TotalHOf.isEven_zero (ZMod p) X

theorem totalP_isEven (X : TopCat.{0}) (i : ℕ) (x : TotalHOf (ZMod p) X) :
    TotalHOf.IsEven (R.totalP X i x) := by
  induction x using DirectSum.induction_on with
  | zero => rw [map_zero]; exact TotalHOf.isEven_zero (ZMod p) X
  | of d c => exact R.totalP_of X i d c ▸ R.pieceP_isEven X i d c
  | add x y hx hy => rw [map_add]; exact hx.add hy

/-! ## The total power on the whole ring -/

/-- The total power on one degree: `ptotOf` in even degree, zero in odd degree. -/
def piecePtot (X : TopCat.{0}) (d : ℕ) : TotalPieceOf (ZMod p) X d →+ TotalHOf (ZMod p) X :=
  if d % 2 = 0 then ptotOf R.D X d else 0

theorem piecePtot_apply (X : TopCat.{0}) (d : ℕ) (c : TotalPieceOf (ZMod p) X d) :
    R.piecePtot X d c = if d % 2 = 0 then ptotOf R.D X d c else 0 := by
  rw [piecePtot]
  by_cases h : d % 2 = 0
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]; rfl

/-- The total power on the whole cohomology ring. -/
def totalPtot (X : TopCat.{0}) : TotalHOf (ZMod p) X →+ TotalHOf (ZMod p) X :=
  DirectSum.toAddMonoid fun d => R.piecePtot X d

theorem totalPtot_of (X : TopCat.{0}) (d : ℕ) (c : TotalPieceOf (ZMod p) X d) :
    R.totalPtot X (TotalHOf.of (ZMod p) X d c) = R.piecePtot X d c :=
  DirectSum.toAddMonoid_of _ _ _

theorem totalPtot_isEven (X : TopCat.{0}) (x : TotalHOf (ZMod p) X) :
    TotalHOf.IsEven (R.totalPtot X x) := by
  induction x using DirectSum.induction_on with
  | zero => rw [map_zero]; exact TotalHOf.isEven_zero (ZMod p) X
  | of d c =>
    rw [show DirectSum.of (fun n : ℕ => TotalPieceOf (ZMod p) X n) d c
        = TotalHOf.of (ZMod p) X d c from rfl, R.totalPtot_of, R.piecePtot_apply]
    by_cases h : d % 2 = 0
    · rw [if_pos h]; exact R.ptotOf_isEven X h c
    · rw [if_neg h]; exact TotalHOf.isEven_zero (ZMod p) X
  | add x y hx hy => rw [map_add]; exact hx.add hy

end TotalReducedPowers

end

end OddPTotal

#audit_axioms OddPTotal.TotalReducedPowers.component_ptotOf
#audit_axioms OddPTotal.TotalReducedPowers.ptotOf_natural
#audit_axioms OddPTotal.TotalReducedPowers.totalP_isEven
#audit_axioms OddPTotal.TotalReducedPowers.totalPtot_isEven

end CharClass
end GroupApproximation
