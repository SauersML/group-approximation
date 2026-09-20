import GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.HL1.DilRel

/-!
# Tulenbaev's dilation on generators: relation (1.3) (T Lemma 3.2)

Relation (1.3) of `St(R, 𝔄R)`: `X_{bv + v', w} = X_{v, bw} X_{v', w}` when `u v = 0`, `u v' = 1` and
`w v = 0`. Write `b = Tʲ b₀` with `b₀ = T⁻ʲ b ∈ B`. For `m, n` large, over `B`:
* `T⁻⁽ᵐ⁺ʲ⁾ (b v + v') = T⁻⁽ᵐ⁺ʲ⁾ v' + b₀ T⁻ᵐ v` (`hcol`) and `Tᵐ⁺ⁿ b w = b₀ Tᵐ⁺ʲ⁺ⁿ w` (`hrow`);
* `TulX.smulRow` moves `b₀` into the parameter, `TulX.colAdd` splits the column, and
  `TulX.commute_X` swaps the two factors (`w` is orthogonal to `v` and `v'`).

`colAdd` needs `Tᵐ⁺ʲ⁺ⁿ w` in the span of the two-zero rows orthogonal to both columns
(`span_twoZero`). That comes from `TwoZero.det_smul_mem_span_twoZero` with rows `P`, `Q` over `B`
whose determinant against the two columns is `T⁻ˢ T⁻ˢ'`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false

namespace GroupApproximation
namespace BooneHigmanLinear
namespace TulenbaevHorrocks
namespace HL1

open Matrix LaurentPolynomial
open GroupApproximation.SteinbergGroup
open GroupApproximation.BooneHigmanLinear.PaninAffine (TulX AdmRow coordIdeal orthSub pMat)
open GroupApproximation.BooneHigmanLinear.K2Found.RelPres (RMem IsEColumn)

variable {A : Type} [CommRing A] {𝔄 : Ideal A} {N : ℕ} (TX : TulX N)

theorem VB.mono {v : Fin N → LaurentPolynomial A} {m m' : ℕ} (hm : VB 𝔄 v m) (h : m ≤ m') :
    VB 𝔄 v m' := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  exact hm.add d

theorem mem_coordIdeal_mono {x : Fin N → BB 𝔄} {n n' : ℕ} (h : tB 𝔄 n ∈ coordIdeal x)
    (hle : n ≤ n') : tB 𝔄 n' ∈ coordIdeal x := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
  exact mem_coordIdeal_add h d

theorem dot_T (a b : ℤ) (f g : Fin N → LaurentPolynomial A) :
    (fun i => T a * f i) ⬝ᵥ (fun i => T b * g i) = T a * T b * (f ⬝ᵥ g) := by
  simp only [dotProduct, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem Wt_dot_vt {v w : Fin N → LaurentPolynomial A} (hw : ∀ i, w i ∈ coeffIdeal 𝔄)
    (hwv : w ⬝ᵥ v = 0) {m : ℕ} (hm : VB 𝔄 v m) (k : ℤ) : Wt hw k ⬝ᵥ vt hm = 0 := by
  apply Subtype.ext
  rw [coe_dotProduct]
  show (fun i => T k * w i) ⬝ᵥ (fun i => T (-(m : ℤ)) * v i) = (0 : LaurentPolynomial A)
  rw [dot_T, hwv, mul_zero]

theorem T_eq_mul {x y z : ℤ} (h : x = y + z) :
    (T x : LaurentPolynomial A) = T y * T z := by
  rw [← T_add, h]

/-- **The span condition of `colAdd`.** For `u v = 0`, `u v' = 1`, `u₁ v = 1` and `w ⊥ v, v'`, the
row `Tᵏ w` is in the span of the two-zero rows orthogonal to `T⁻⁽ᵐ⁺ʲ⁾ v'` and `T⁻ᵐ v`. -/
theorem span_twoZero (h5 : 5 ≤ N) {v v' w u u₁ : Fin N → LaurentPolynomial A}
    (hu : u ⬝ᵥ v = 0) (hu' : u ⬝ᵥ v' = 1) (hu₁ : u₁ ⬝ᵥ v = 1) (hwv : w ⬝ᵥ v = 0)
    (hwv' : w ⬝ᵥ v' = 0) (hw : ∀ i, w i ∈ coeffIdeal 𝔄) {m j : ℕ} (hm : VB 𝔄 v m)
    (hm' : VB 𝔄 v' (m + j)) (k : ℤ) :
    Wt hw k ∈ Submodule.span (BB 𝔄) (K2Found.TwoZero.twoZeroSet (vt hm') (vt hm)) := by
  obtain ⟨s, hs⟩ := exists_T_neg_smul_mem (𝔄 := 𝔄) fun i => T (((m + j : ℕ)) : ℤ) * u i
  obtain ⟨s', hs'⟩ := exists_T_neg_smul_mem (𝔄 := 𝔄) fun i => T (m : ℤ) * u₁ i
  obtain ⟨P, hP⟩ : ∃ P : Fin N → BB 𝔄,
      ∀ i, (P i : LaurentPolynomial A) = T (-(s : ℤ)) * (T (((m + j : ℕ)) : ℤ) * u i) :=
    ⟨fun i => ⟨_, hs s le_rfl i⟩, fun i => rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : Fin N → BB 𝔄,
      ∀ i, (Q i : LaurentPolynomial A) = T (-(s' : ℤ)) * (T (m : ℤ) * u₁ i) :=
    ⟨fun i => ⟨_, hs' s' le_rfl i⟩, fun i => rfl⟩
  have e1 : ∀ (a c : ℤ) (f : Fin N → LaurentPolynomial A) (x : Fin N → BB 𝔄) (b : ℤ)
      (g : Fin N → LaurentPolynomial A), (∀ i, (x i : LaurentPolynomial A) = T a * (T c * f i)) →
      (∀ (y : Fin N → BB 𝔄), (∀ i, (y i : LaurentPolynomial A) = T b * g i) →
        ((x ⬝ᵥ y : BB 𝔄) : LaurentPolynomial A) = T a * T c * T b * (f ⬝ᵥ g)) := by
    intro a c f x b g hx y hy
    rw [coe_dotProduct]
    simp only [hx, hy, dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hPv' : P ⬝ᵥ vt hm' = tB 𝔄 s := by
    apply Subtype.ext
    show _ = (T (-(s : ℤ)) : LaurentPolynomial A)
    rw [e1 (-(s : ℤ)) (((m + j : ℕ)) : ℤ) u P (-(((m + j : ℕ)) : ℤ)) v' hP (vt hm') (fun i => rfl),
      hu', mul_one, mul_assoc, ← T_add,
      show (((m + j : ℕ)) : ℤ) + -(((m + j : ℕ)) : ℤ) = 0 by ring, T_zero, mul_one]
  have hPv : P ⬝ᵥ vt hm = 0 := by
    apply Subtype.ext
    show _ = (0 : LaurentPolynomial A)
    rw [e1 (-(s : ℤ)) (((m + j : ℕ)) : ℤ) u P (-(m : ℤ)) v hP (vt hm) (fun i => rfl), hu, mul_zero]
  have hQv : Q ⬝ᵥ vt hm = tB 𝔄 s' := by
    apply Subtype.ext
    show _ = (T (-(s' : ℤ)) : LaurentPolynomial A)
    rw [e1 (-(s' : ℤ)) (m : ℤ) u₁ Q (-(m : ℤ)) v hQ (vt hm) (fun i => rfl), hu₁, mul_one, mul_assoc,
      ← T_add, show (m : ℤ) + -(m : ℤ) = 0 by ring, T_zero, mul_one]
  have hmem := K2Found.TwoZero.det_smul_mem_span_twoZero (by rw [Fintype.card_fin]; exact h5)
    (vt hm') (vt hm) (Wt hw (k + s + s')) P Q (Wt_dot_vt hw hwv' hm' _) (Wt_dot_vt hw hwv hm _)
  rw [hPv', hQv, hPv, mul_zero, sub_zero] at hmem
  have hsmul : (tB 𝔄 s * tB 𝔄 s') • Wt hw (k + s + s') = Wt hw k := by
    funext i
    apply Subtype.ext
    show T (-(s : ℤ)) * T (-(s' : ℤ)) * (T (k + s + s') * w i) = T k * w i
    rw [← mul_assoc, ← T_add, ← T_add, show -(s : ℤ) + -(s' : ℤ) + (k + s + s') = k by ring]
  rwa [hsmul] at hmem

#audit_axioms span_twoZero

/-- **Relation (1.3).** -/
theorem dgen_frame (h5 : 5 ≤ N) (v v' w u : Fin N → LaurentPolynomial A) (b : LaurentPolynomial A)
    (hu : u ⬝ᵥ v = 0) (hu' : u ⬝ᵥ v' = 1) (hw : w ⬝ᵥ v = 0)
    (h₁ : RMem (coeffIdeal 𝔄) (b • v + v', w)) (h₂ : RMem (coeffIdeal 𝔄) (v, b • w))
    (h₃ : RMem (coeffIdeal 𝔄) (v', w)) :
    dgen TX (b • v + v', w) h₁ = dgen TX (v, b • w) h₂ * dgen TX (v', w) h₃ := by
  obtain ⟨u₁, hu₁⟩ : ∃ u₁ : Fin N → LaurentPolynomial A, u₁ ⬝ᵥ v = 1 := h₂.1.isUnimodular
  obtain ⟨u₂, hu₂⟩ : ∃ u₂ : Fin N → LaurentPolynomial A, u₂ ⬝ᵥ (b • v + v') = 1 :=
    h₁.1.isUnimodular
  have hwv' : w ⬝ᵥ v' = 0 := h₃.2.2
  have hw₃ : ∀ i, w i ∈ coeffIdeal 𝔄 := h₃.2.1
  obtain ⟨b₀, hb₀⟩ : ∃ b₀ : BB 𝔄, (b₀ : LaurentPolynomial A) = T (-(topDeg b : ℤ)) * b :=
    ⟨⟨_, T_neg_mul_mem le_rfl⟩, rfl⟩
  obtain ⟨ma, hma, -, -⟩ := exists_valid_of_rmem h₂
  obtain ⟨mb, hmb, -, -⟩ := exists_valid_of_rmem h₃
  obtain ⟨mc, hmc, -, -⟩ := exists_valid_of_rmem h₁
  obtain ⟨m, hmv, hmv', hmvc⟩ : ∃ m : ℕ, VB 𝔄 v m ∧ VB 𝔄 v' (m + topDeg b) ∧
      VB 𝔄 (b • v + v') (m + topDeg b) :=
    ⟨ma + mb + mc, VB.mono hma (by omega), VB.mono hmb (by omega), VB.mono hmc (by omega)⟩
  obtain ⟨na, hna⟩ := exists_n hu₁ hmv
  obtain ⟨nb, hnb⟩ := exists_n hu' hmv'
  obtain ⟨nc, hnc⟩ := exists_n hu₂ hmvc
  obtain ⟨n, hta, htb, htc⟩ : ∃ n : ℕ, tB 𝔄 n ∈ coordIdeal (vt hmv) ∧
      tB 𝔄 n ∈ coordIdeal (vt hmv') ∧ tB 𝔄 n ∈ coordIdeal (vt hmvc) :=
    ⟨na + nb + nc, mem_coordIdeal_mono hna (by omega), mem_coordIdeal_mono hnb (by omega),
      mem_coordIdeal_mono hnc (by omega)⟩
  have hcol : vt hmvc = vt hmv' + b₀ • vt hmv := by
    funext i
    apply Subtype.ext
    show T (-(((m + topDeg b : ℕ)) : ℤ)) * (b * v i + v' i) =
      T (-(((m + topDeg b : ℕ)) : ℤ)) * v' i + (b₀ : LaurentPolynomial A) * (T (-(m : ℤ)) * v i)
    rw [hb₀, T_eq_mul (x := -(((m + topDeg b : ℕ)) : ℤ)) (y := -(topDeg b : ℤ)) (z := -(m : ℤ))
      (by push_cast; ring)]
    ring
  have hrow : Wt h₂.2.1 ((m : ℤ) + n) = b₀ • Wt hw₃ ((((m + topDeg b : ℕ)) : ℤ) + n) := by
    funext i
    apply Subtype.ext
    show T ((m : ℤ) + n) * (b * w i) =
      (b₀ : LaurentPolynomial A) * (T ((((m + topDeg b : ℕ)) : ℤ) + n) * w i)
    rw [hb₀, T_eq_mul (x := (m : ℤ) + n) (y := -(topDeg b : ℤ))
      (z := (((m + topDeg b : ℕ)) : ℤ) + n) (by push_cast; ring)]
    ring
  have hadm : AdmRow (vt hmv) (Wt hw₃ ((((m + topDeg b : ℕ)) : ℤ) + n)) :=
    adm_Wt hu₁ hw hw₃ hmv _
  have hadm' : AdmRow (vt hmv') (Wt hw₃ ((((m + topDeg b : ℕ)) : ℤ) + n)) :=
    adm_Wt hu' hwv' hw₃ hmv' _
  have hspan := span_twoZero h5 hu hu' hu₁ hw hwv' hw₃ hmv hmv'
    ((((m + topDeg b : ℕ)) : ℤ) + n)
  have htc' : tB 𝔄 n ∈ coordIdeal (vt hmv' + b₀ • vt hmv) := by
    rw [← hcol]
    exact htc
  have hWt : Wt h₁.2.1 ((((m + topDeg b : ℕ)) : ℤ) + n) = Wt hw₃ ((((m + topDeg b : ℕ)) : ℤ) + n) :=
    rfl
  rw [dgen_eq TX h₁ hmvc htc, dgen_eq TX h₂ hmv hta, dgen_eq TX h₃ hmv' htb]
  unfold val
  rw [hrow, TX.smulRow _ _ _ _ hadm hta, hcol, hWt,
    TX.colAdd _ _ _ _ _ hspan htb (Ideal.mul_mem_left _ _ hta) htc']
  exact (TX.commute_X _ _ _ _ _ _ hadm' htb hadm (Ideal.mul_mem_left _ _ hta)
    (Wt_dot_vt hw₃ hwv' hmv' _) (Wt_dot_vt hw₃ hw hmv _)).eq

#audit_axioms dgen_frame

end HL1
end TulenbaevHorrocks
end BooneHigmanLinear
end GroupApproximation
