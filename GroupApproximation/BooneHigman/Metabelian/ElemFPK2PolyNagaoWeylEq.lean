import GroupApproximation.BooneHigman.Metabelian.ElemFPK2PolyNagaoWeylTail
import GroupApproximation.Meta.AxiomGuard

/-!
# The Weyl check of `σ`, part 7: the columns with `deg b = deg a`

Lane `bh-met-93d`.  Notation of `ElemFPK2PolyNagaoWeylLt`.  Let `(a, b)` be coprime, `b ≠ 0`,
`deg b = deg a`.  Write `b = γ a + r` with `γ ∈ F_pˣ` the ratio of leading coefficients and
`deg r < deg a`; put `δ = -γ⁻¹`.  Then
`b / a = γ`, `b % a = r`, `a / (-b) = δ`, `a % (-b) = δ r`, so
`pair a b = x'(γ) W pair r (-a)` and `pair (-b) a = x'(δ) W pair (δ r) b`, and

  `D(a, b) = (pair (δ r) b)⁻¹ · (W⁻¹ x'(-δ) W x'(γ) W) · pair r (-a)`.

As `γ = -δ⁻¹`, the middle identity (`k2PolyNagaoWeyl_middle`) makes the bracket `t(δ) x'(δ)`,
and the two tails of `ElemFPK2PolyNagaoWeylTail` finish.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.SteinbergGroup
open GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergWeyl (w)

variable {I : Type} [Fintype I] [DecidableEq I] {p : ℕ} [Fact p.Prime]

/-- `b ≠ 0` and `deg b = deg a` force `a ≠ 0`. -/
theorem k2PolyNagaoWeyl_ne_zero_of_degree_eq {a b : Polynomial (ZMod p)} (hb : b ≠ 0)
    (hdeq : b.degree = a.degree) : a ≠ 0 := by
  rintro rfl
  rw [Polynomial.degree_zero] at hdeq
  exact hb (Polynomial.degree_eq_bot.1 hdeq)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoWeyl_ne_zero_of_degree_eq

/-- Equal degrees: some constant `γ` makes `deg (b - γ a) < deg a`. -/
theorem k2PolyNagaoWeyl_eq_data {a b : Polynomial (ZMod p)} (hb : b ≠ 0)
    (hdeq : b.degree = a.degree) :
    ∃ γ : (ZMod p)ˣ, (b - Polynomial.C (γ : ZMod p) * a).degree < a.degree := by
  have hla : a.leadingCoeff ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.2 (k2PolyNagaoWeyl_ne_zero_of_degree_eq hb hdeq)
  have hlb : b.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.2 hb
  obtain ⟨γ, hγ⟩ : ∃ γ : (ZMod p)ˣ, (γ : ZMod p) = b.leadingCoeff * a.leadingCoeff⁻¹ :=
    ⟨Units.mk0 _ (mul_ne_zero hlb (inv_ne_zero hla)), Units.val_mk0 _⟩
  have hlc : b.leadingCoeff = (Polynomial.C (γ : ZMod p) * a).leadingCoeff := by
    rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, hγ, mul_assoc,
      inv_mul_cancel₀ hla, mul_one]
  have hdq : b.degree = (Polynomial.C (γ : ZMod p) * a).degree := by
    rw [Polynomial.degree_C_mul γ.ne_zero, hdeq]
  refine ⟨γ, ?_⟩
  rw [← hdeq]
  exact Polynomial.degree_sub_lt hdq hb hlc

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoWeyl_eq_data

variable {m L n : I} (hmL : m ≠ L) (hmn : m ≠ n) (hLn : L ≠ n)

include hmn hLn

/-- **Case `deg b = deg a`.**  The check element at a coprime column `(a, b)` with `b ≠ 0` and
`deg b = deg a` lies in `Q`. -/
theorem k2PolyNagaoWeyl_check_pair_eq {K : Finset I} (hmK : m ∈ K) {a b : Polynomial (ZMod p)}
    (hab : IsCoprime a b) (hb : b ≠ 0) (hdeq : b.degree = a.degree) :
    (k2PolyNagaoSigma_pair p m L hmL (-b) a)⁻¹ * w m L hmL (-1 : (Polynomial (ZMod p))ˣ) *
      k2PolyNagaoSigma_pair p m L hmL a b ∈ k2PolyNF_Q p K L := by
  have ha : a ≠ 0 := k2PolyNagaoWeyl_ne_zero_of_degree_eq hb hdeq
  obtain ⟨γ, hrlt⟩ := k2PolyNagaoWeyl_eq_data hb hdeq
  obtain ⟨r, hr_def⟩ : ∃ r, r = b - Polynomial.C (γ : ZMod p) * a := ⟨_, rfl⟩
  rw [← hr_def] at hrlt
  obtain ⟨hq1, hr1⟩ := k2PolyNagaoWeyl_divmod_unique (b := b) (q := Polynomial.C (γ : ZMod p))
    ha (by linear_combination -hr_def) hrlt
  obtain ⟨δ, hδ⟩ : ∃ δ : (ZMod p)ˣ, δ = -γ⁻¹ := ⟨_, rfl⟩
  have hδinv : Polynomial.C ((δ⁻¹ : (ZMod p)ˣ) : ZMod p) = -Polynomial.C (γ : ZMod p) := by
    rw [hδ, inv_neg, inv_inv, Units.val_neg, map_neg]
  have hδγ : Polynomial.C (δ : ZMod p) * Polynomial.C (γ : ZMod p) = -1 := by
    rw [← map_mul Polynomial.C, ← Units.val_mul, hδ, neg_mul, inv_mul_cancel, Units.val_neg,
      Units.val_one, map_neg, map_one]
  have hdeg2 : (Polynomial.C (δ : ZMod p) * r).degree < (-b).degree := by
    rw [Polynomial.degree_C_mul δ.ne_zero, Polynomial.degree_neg, hdeq]
    exact hrlt
  obtain ⟨hq2, hr2⟩ := k2PolyNagaoWeyl_divmod_unique (b := a) (q := Polynomial.C (δ : ZMod p))
    (neg_ne_zero.2 hb)
    (by linear_combination -Polynomial.C (δ : ZMod p) * hr_def + a * hδγ) hdeg2
  have hM : (w m L hmL (-1 : (Polynomial (ZMod p))ˣ))⁻¹ *
      x L m hmL.symm (-Polynomial.C (δ : ZMod p)) * w m L hmL (-1 : (Polynomial (ZMod p))ˣ) *
        x L m hmL.symm (Polynomial.C (γ : ZMod p)) * w m L hmL (-1 : (Polynomial (ZMod p))ˣ) =
      k2PolyDeg_torus p m L n hmL hmn hLn δ * x L m hmL.symm (Polynomial.C (δ : ZMod p)) := by
    rw [show Polynomial.C (γ : ZMod p) = -Polynomial.C ((δ⁻¹ : (ZMod p)ˣ) : ZMod p) by
      rw [hδinv, neg_neg], k2PolyDeg_torus_apply]
    exact k2PolyNagaoWeyl_middle hmL hmn hLn
      (Units.map (Polynomial.C : ZMod p →+* Polynomial (ZMod p)).toMonoidHom δ)
  have gid : ∀ X Y V P1 P2 : SteinbergGroup I (Polynomial (ZMod p)),
      (X * V * P1)⁻¹ * V * (Y * V * P2) = P1⁻¹ * (V⁻¹ * X⁻¹ * V * Y * V * P2) :=
    fun X Y V P1 P2 => by group
  rw [k2PolyNagaoSigma_pair_of_ne p m L hmL ha, hq1, hr1,
    k2PolyNagaoSigma_pair_of_ne p m L hmL (neg_ne_zero.2 hb), hq2, hr2, neg_neg, gid, ← x_neg,
    hM]
  by_cases hr0 : r = 0
  · subst hr0
    have hb_eq : b = Polynomial.C (γ : ZMod p) * a := by linear_combination -hr_def
    obtain ⟨u, v, huv⟩ := hab
    have hua : IsUnit a :=
      isUnit_of_dvd_one ⟨u + v * Polynomial.C (γ : ZMod p), by linear_combination -huv + v * hb_eq⟩
    obtain ⟨α, rfl⟩ := k2PolyNagaoWeyl_exists_C_of_isUnit hua
    subst hb_eq
    have hu : γ * α * δ = -α := by
      rw [hδ, mul_neg, mul_comm γ α, mul_assoc, mul_inv_cancel, mul_one]
    exact k2PolyNagaoWeyl_eq_tail_zero hmL hmn hLn hmK α γ δ hu
  · rw [k2PolyNagaoWeyl_eq_tail_ne hmL hmn hLn γ δ hab hr0 hr_def hδγ hδinv]
    exact (k2PolyNF_Q p K L).one_mem

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoWeyl_check_pair_eq

end GroupApproximation.BooneHigman.Metabelian.ElemFP
