import GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.HL1.Laurent
import GroupApproximation.BooneHigmanLinear.PaninAffine.TulX

/-!
# The values of Tulenbaev's dilation (T Lemma 3.2), and their independence of the choices

`R = A[T, T⁻¹]`, `B = A[T⁻¹] + 𝔄[T]` (`BB 𝔄`), `TX` an instance of Tulenbaev's elements
`X_{v,w}(t)` (`PaninAffine.TulX N`). Let `v` be a column over `R` with `u v = 1` for some row `u`,
and `w` a row with entries in `𝔄R` and `w v = 0`. Tulenbaev's Lemma 3.2 sends the generator
`X_{v,w}` of `St(R, 𝔄R)` to `X_{T⁻ᵐ v, Tᵐ⁺ⁿ w}(T⁻ⁿ) ∈ St(B)`, for `m, n` large.

* `VB 𝔄 v m`: `T⁻ᵐ v` has entries in `B`; `vt hm` is that column over `B`. `Wt hw k = Tᵏ w` over `B`
  (every row with entries in `𝔄R` lies over `B`).
* `adm_Wt`: `Tᵏ w` is admissible for `T⁻ᵐ v`, i.e. in `I(T⁻ᵐ v) · (T⁻ᵐ v)^⊥`.
* `val TX hw hm n = X_{T⁻ᵐ v, Tᵐ⁺ⁿ w}(T⁻ⁿ)`. A pair `(m, n)` is *valid* when `VB 𝔄 v m` and
  `T⁻ⁿ ∈ I(T⁻ᵐ v)`.
* `val_succ_n` and `val_succ_m`: `(m, n) ~ (m, n + 1)` and `(m + 1, n) ~ (m, n + 1)`, from `smulRow` and
  `smulCol` with `c = T⁻¹ ∈ B`.
* `val_indep`: all valid pairs give the same value. `exists_valid`: a valid pair exists.
  `gval` is the common value, and `gval_eq` says that every valid pair gives it.
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
open GroupApproximation.BooneHigmanLinear.PaninAffine (TulX AdmRow coordIdeal orthSub)

variable {A : Type} [CommRing A] {𝔄 : Ideal A} {N : ℕ}

/-- `B = A[T⁻¹] + 𝔄[T]`, as a type. -/
abbrev BB (𝔄 : Ideal A) : Type :=
  ↥(Graded.horrB 𝔄)

/-- `T⁻ⁿ ∈ B`. -/
def tB (𝔄 : Ideal A) (n : ℕ) : BB 𝔄 :=
  ⟨T (-(n : ℤ)), T_neg_mem n⟩

theorem T_neg_succ (n : ℕ) :
    (T (-((n + 1 : ℕ) : ℤ)) : LaurentPolynomial A) = T (-((1 : ℕ) : ℤ)) * T (-(n : ℤ)) := by
  rw [← T_add, show -((1 : ℕ) : ℤ) + -(n : ℤ) = -((n + 1 : ℕ) : ℤ) by push_cast; ring]

theorem tB_succ (n : ℕ) : tB 𝔄 (n + 1) = tB 𝔄 1 * tB 𝔄 n := by
  apply Subtype.ext
  show (T (-((n + 1 : ℕ) : ℤ)) : LaurentPolynomial A) = T (-((1 : ℕ) : ℤ)) * T (-(n : ℤ))
  exact T_neg_succ n

theorem coe_dotProduct (x y : Fin N → BB 𝔄) :
    ((x ⬝ᵥ y : BB 𝔄) : LaurentPolynomial A) =
      (fun i => (x i : LaurentPolynomial A)) ⬝ᵥ (fun i => (y i : LaurentPolynomial A)) :=
  RingHom.map_dotProduct (Graded.horrB 𝔄).subtype x y

theorem dotProduct_mem_coordIdeal (u x : Fin N → BB 𝔄) : u ⬝ᵥ x ∈ coordIdeal x := by
  show ∑ i, u i * x i ∈ coordIdeal x
  exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)

theorem mem_coordIdeal_succ {x : Fin N → BB 𝔄} {n : ℕ} (h : tB 𝔄 n ∈ coordIdeal x) :
    tB 𝔄 (n + 1) ∈ coordIdeal x := by
  rw [tB_succ]
  exact Ideal.mul_mem_left _ _ h

theorem mem_coordIdeal_add {x : Fin N → BB 𝔄} {n : ℕ} (h : tB 𝔄 n ∈ coordIdeal x) :
    ∀ k : ℕ, tB 𝔄 (n + k) ∈ coordIdeal x
  | 0 => h
  | k + 1 => mem_coordIdeal_succ (mem_coordIdeal_add h k)

theorem coordIdeal_smul_le (c : BB 𝔄) (x : Fin N → BB 𝔄) : coordIdeal (c • x) ≤ coordIdeal x := by
  refine Ideal.span_le.2 ?_
  rintro _ ⟨i, rfl⟩
  exact Ideal.mul_mem_left _ c (Ideal.subset_span ⟨i, rfl⟩)

/-! ### The columns `T⁻ᵐ v` and rows `Tᵏ w` over `B` -/

/-- `T⁻ᵐ v` has entries in `B`. -/
def VB (𝔄 : Ideal A) (v : Fin N → LaurentPolynomial A) (m : ℕ) : Prop :=
  ∀ i, T (-(m : ℤ)) * v i ∈ Graded.horrB 𝔄

theorem VB.succ {v : Fin N → LaurentPolynomial A} {m : ℕ} (hm : VB 𝔄 v m) : VB 𝔄 v (m + 1) :=
  fun i => by
    rw [T_neg_succ, mul_assoc]
    exact Subring.mul_mem _ (T_neg_mem 1) (hm i)

theorem VB.add {v : Fin N → LaurentPolynomial A} {m : ℕ} (hm : VB 𝔄 v m) :
    ∀ d : ℕ, VB 𝔄 v (m + d)
  | 0 => hm
  | d + 1 => (VB.add hm d).succ

/-- `T⁻ᵐ v` over `B`. -/
def vt {v : Fin N → LaurentPolynomial A} {m : ℕ} (hm : VB 𝔄 v m) : Fin N → BB 𝔄 :=
  fun i => ⟨T (-(m : ℤ)) * v i, hm i⟩

theorem vt_succ {v : Fin N → LaurentPolynomial A} {m : ℕ} (hm : VB 𝔄 v m) :
    vt hm.succ = tB 𝔄 1 • vt hm := by
  funext i
  apply Subtype.ext
  show T (-((m + 1 : ℕ) : ℤ)) * v i = T (-((1 : ℕ) : ℤ)) * (T (-(m : ℤ)) * v i)
  rw [T_neg_succ, mul_assoc]

/-- `Tᵏ w` over `B`, for `w` with entries in `𝔄R`. -/
def Wt {w : Fin N → LaurentPolynomial A} (hw : ∀ i, w i ∈ coeffIdeal 𝔄) (k : ℤ) :
    Fin N → BB 𝔄 :=
  fun i => ⟨T k * w i, coeffIdeal_le_horrB (Ideal.mul_mem_left _ _ (hw i))⟩

theorem Wt_eq_smul {w : Fin N → LaurentPolynomial A} (hw : ∀ i, w i ∈ coeffIdeal 𝔄) (k : ℤ) :
    Wt hw k = tB 𝔄 1 • Wt hw (k + 1) := by
  funext i
  apply Subtype.ext
  show T k * w i = T (-((1 : ℕ) : ℤ)) * (T (k + 1) * w i)
  rw [← mul_assoc, ← T_add, show -((1 : ℕ) : ℤ) + (k + 1) = k by push_cast; ring]

/-- The rows `Tᵐ uⱼ Tᵏ w` of the decomposition in `adm_Wt`. -/
def yRow {u w : Fin N → LaurentPolynomial A} (hw : ∀ i, w i ∈ coeffIdeal 𝔄) (m : ℕ) (k : ℤ)
    (j : Fin N) : Fin N → BB 𝔄 :=
  fun i => ⟨T (m : ℤ) * u j * (T k * w i),
    coeffIdeal_le_horrB (Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ (hw i)))⟩

theorem T_neg_mul_T (m : ℕ) : (T (-(m : ℤ)) : LaurentPolynomial A) * T (m : ℤ) = 1 := by
  rw [← T_add, neg_add_cancel, T_zero]

/-- **Admissibility.** `Tᵏ w ∈ I(T⁻ᵐ v) · (T⁻ᵐ v)^⊥`, via `Tᵏ w = ∑ⱼ (T⁻ᵐ vⱼ)(Tᵐ uⱼ Tᵏ w)`. -/
theorem adm_Wt {u v w : Fin N → LaurentPolynomial A} (hu : u ⬝ᵥ v = 1) (hwv : w ⬝ᵥ v = 0)
    (hw : ∀ i, w i ∈ coeffIdeal 𝔄) {m : ℕ} (hm : VB 𝔄 v m) (k : ℤ) :
    AdmRow (vt hm) (Wt hw k) := by
  have hy : ∀ j, yRow (u := u) hw m k j ∈ orthSub (vt hm) := by
    intro j
    show yRow (u := u) hw m k j ⬝ᵥ vt hm = 0
    apply Subtype.ext
    rw [coe_dotProduct]
    show ∑ i, T (m : ℤ) * u j * (T k * w i) * (T (-(m : ℤ)) * v i) = (0 : LaurentPolynomial A)
    have e : ∑ i, T (m : ℤ) * u j * (T k * w i) * (T (-(m : ℤ)) * v i) =
        (T (m : ℤ) * u j * T k * T (-(m : ℤ))) * (w ⬝ᵥ v) := by
      rw [dotProduct, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e, hwv, mul_zero]
  have hsum : Wt hw k = ∑ j, vt hm j • yRow (u := u) hw m k j := by
    funext i
    apply Subtype.ext
    have e : ((∑ j, vt hm j • yRow (u := u) hw m k j) i : BB 𝔄) =
        ∑ j, vt hm j * yRow (u := u) hw m k j i := by
      rw [Finset.sum_apply]
      rfl
    rw [e]
    show T k * w i = (Graded.horrB 𝔄).subtype (∑ j, vt hm j * yRow (u := u) hw m k j i)
    rw [map_sum]
    show T k * w i = ∑ j, T (-(m : ℤ)) * v j * (T (m : ℤ) * u j * (T k * w i))
    have hu' : ∑ j, u j * v j = 1 := hu
    calc T k * w i = (∑ j, u j * v j) * (T k * w i) := by rw [hu', one_mul]
      _ = ∑ j, T (-(m : ℤ)) * v j * (T (m : ℤ) * u j * (T k * w i)) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        calc u j * v j * (T k * w i)
            = (T (-(m : ℤ)) * T (m : ℤ)) * (u j * v j * (T k * w i)) := by
              rw [T_neg_mul_T, one_mul]
          _ = T (-(m : ℤ)) * v j * (T (m : ℤ) * u j * (T k * w i)) := by ring
  show Wt hw k ∈ coordIdeal (vt hm) • orthSub (vt hm)
  rw [hsum]
  exact Submodule.sum_mem _ fun j _ =>
    Submodule.smul_mem_smul (PaninAffine.mem_coordIdeal j) (hy j)

#audit_axioms adm_Wt

/-! ### The values and their independence -/

variable (TX : TulX N)

/-- `X_{T⁻ᵐ v, Tᵐ⁺ⁿ w}(T⁻ⁿ) ∈ St(B)`. -/
noncomputable def val {v w : Fin N → LaurentPolynomial A} (hw : ∀ i, w i ∈ coeffIdeal 𝔄)
    {m : ℕ} (hm : VB 𝔄 v m) (n : ℕ) : SteinbergGroup (Fin N) (BB 𝔄) :=
  TX.X (vt hm) (Wt hw ((m : ℤ) + n)) (tB 𝔄 n)

variable {u v w : Fin N → LaurentPolynomial A} (hu : u ⬝ᵥ v = 1) (hwv : w ⬝ᵥ v = 0)
  (hw : ∀ i, w i ∈ coeffIdeal 𝔄)

include hu hwv in
/-- `(m, n) ~ (m, n + 1)`. -/
theorem val_succ_n {m : ℕ} (hm : VB 𝔄 v m) {n : ℕ} (ht : tB 𝔄 n ∈ coordIdeal (vt hm)) :
    val TX hw hm n = val TX hw hm (n + 1) := by
  unfold val
  rw [Wt_eq_smul hw ((m : ℤ) + n), TX.smulRow _ _ _ _ (adm_Wt hu hwv hw hm _) ht, ← tB_succ,
    show (m : ℤ) + n + 1 = (m : ℤ) + ((n + 1 : ℕ) : ℤ) by push_cast; ring]

include hu hwv in
/-- `(m + 1, n) ~ (m, n + 1)`. -/
theorem val_succ_m {m : ℕ} (hm : VB 𝔄 v m) {n : ℕ} (ht : tB 𝔄 n ∈ coordIdeal (vt hm.succ)) :
    val TX hw hm.succ n = val TX hw hm (n + 1) := by
  unfold val
  rw [vt_succ hm] at ht ⊢
  rw [TX.smulCol _ _ _ _ (adm_Wt hu hwv hw hm _) ht, ← tB_succ,
    show ((m + 1 : ℕ) : ℤ) + n = (m : ℤ) + ((n + 1 : ℕ) : ℤ) by push_cast; ring]

include hu hwv in
theorem val_eq_add {m : ℕ} (hm : VB 𝔄 v m) {n : ℕ} (ht : tB 𝔄 n ∈ coordIdeal (vt hm)) :
    ∀ k : ℕ, val TX hw hm n = val TX hw hm (n + k)
  | 0 => rfl
  | k + 1 => (val_eq_add hm ht k).trans (val_succ_n TX hu hwv hw hm (mem_coordIdeal_add ht k))

include hu hwv in
theorem val_eq_same {m : ℕ} (hm : VB 𝔄 v m) {n n' : ℕ} (ht : tB 𝔄 n ∈ coordIdeal (vt hm))
    (ht' : tB 𝔄 n' ∈ coordIdeal (vt hm)) : val TX hw hm n = val TX hw hm n' := by
  rcases le_total n n' with h | h
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    exact val_eq_add TX hu hwv hw hm ht k
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    exact (val_eq_add TX hu hwv hw hm ht' k).symm

include hu hwv in
theorem val_eq_up {m : ℕ} (hm : VB 𝔄 v m) {n : ℕ} (ht : tB 𝔄 n ∈ coordIdeal (vt hm)) :
    ∀ (d : ℕ) (n' : ℕ), tB 𝔄 n' ∈ coordIdeal (vt (hm.add d)) →
      val TX hw hm n = val TX hw (hm.add d) n'
  | 0, n', htd => val_eq_same TX hu hwv hw hm ht htd
  | d + 1, n', htd => by
    have htd' : tB 𝔄 n' ∈ coordIdeal (vt (hm.add d).succ) := htd
    have h1 : val TX hw (hm.add (d + 1)) n' = val TX hw (hm.add d) (n' + 1) :=
      val_succ_m TX hu hwv hw (hm.add d) htd'
    have h2 : tB 𝔄 (n' + 1) ∈ coordIdeal (vt (hm.add d)) := by
      rw [vt_succ] at htd'
      exact mem_coordIdeal_succ (coordIdeal_smul_le _ _ htd')
    rw [h1]
    exact val_eq_up hm ht d (n' + 1) h2

include hu hwv in
/-- **Independence.** All valid pairs `(m, n)` give the same value. -/
theorem val_indep {m m' : ℕ} (hm : VB 𝔄 v m) (hm' : VB 𝔄 v m') {n n' : ℕ}
    (ht : tB 𝔄 n ∈ coordIdeal (vt hm)) (ht' : tB 𝔄 n' ∈ coordIdeal (vt hm')) :
    val TX hw hm n = val TX hw hm' n' := by
  rcases le_total m m' with h | h
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    exact val_eq_up TX hu hwv hw hm ht d n' ht'
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    exact (val_eq_up TX hu hwv hw hm' ht' d n ht).symm

#audit_axioms val_indep

/-- The row `T⁻ʲ' Tʲ u` over `B`. -/
def uRow {u : Fin N → LaurentPolynomial A} {j j' : ℕ}
    (h : ∀ i, T (-(j' : ℤ)) * (T (j : ℤ) * u i) ∈ Graded.horrB 𝔄) : Fin N → BB 𝔄 :=
  fun i => ⟨T (-(j' : ℤ)) * (T (j : ℤ) * u i), h i⟩

/-- For `T⁻ʲ v` over `B` there is `n` with `T⁻ⁿ ∈ I(T⁻ʲ v)`: take `n` with `T⁻ⁿ⁺ʲ u` over `B`. -/
theorem exists_n {u v : Fin N → LaurentPolynomial A} (hu : u ⬝ᵥ v = 1) {j : ℕ} (hm : VB 𝔄 v j) :
    ∃ n : ℕ, tB 𝔄 n ∈ coordIdeal (vt hm) := by
  obtain ⟨j', hj'⟩ := exists_T_neg_smul_mem (𝔄 := 𝔄) fun i => T (j : ℤ) * u i
  refine ⟨j', ?_⟩
  have e : tB 𝔄 j' = uRow (hj' j' le_rfl) ⬝ᵥ vt hm := by
    apply Subtype.ext
    rw [coe_dotProduct]
    show T (-(j' : ℤ)) = ∑ i, T (-(j' : ℤ)) * (T (j : ℤ) * u i) * (T (-(j : ℤ)) * v i)
    have hu' : ∑ i, u i * v i = 1 := hu
    calc (T (-(j' : ℤ)) : LaurentPolynomial A) = T (-(j' : ℤ)) * (∑ i, u i * v i) := by
          rw [hu', mul_one]
      _ = ∑ i, T (-(j' : ℤ)) * (T (j : ℤ) * u i) * (T (-(j : ℤ)) * v i) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        calc T (-(j' : ℤ)) * (u i * v i)
            = T (-(j' : ℤ)) * (u i * v i) * (T (-(j : ℤ)) * T (j : ℤ)) := by
              rw [T_neg_mul_T, mul_one]
          _ = T (-(j' : ℤ)) * (T (j : ℤ) * u i) * (T (-(j : ℤ)) * v i) := by ring
  rw [e]
  exact dotProduct_mem_coordIdeal _ (vt hm)

theorem exists_valid (𝔄 : Ideal A) {u v : Fin N → LaurentPolynomial A} (hu : u ⬝ᵥ v = 1) :
    ∃ (m : ℕ) (hm : VB 𝔄 v m) (n : ℕ), tB 𝔄 n ∈ coordIdeal (vt hm) := by
  obtain ⟨j, hj⟩ := exists_T_neg_smul_mem (𝔄 := 𝔄) v
  have hm : VB 𝔄 v j := hj j le_rfl
  exact ⟨j, hm, exists_n hu hm⟩

/-- The common value of `val` over the valid pairs. -/
noncomputable def gval (𝔄 : Ideal A) {u v w : Fin N → LaurentPolynomial A} (hu : u ⬝ᵥ v = 1)
    (hw : ∀ i, w i ∈ coeffIdeal 𝔄) : SteinbergGroup (Fin N) (BB 𝔄) :=
  val TX hw (exists_valid 𝔄 hu).choose_spec.fst (exists_valid 𝔄 hu).choose_spec.snd.choose

include hwv in
theorem gval_eq {m : ℕ} (hm : VB 𝔄 v m) {n : ℕ} (ht : tB 𝔄 n ∈ coordIdeal (vt hm)) :
    gval TX 𝔄 hu hw = val TX hw hm n :=
  val_indep TX hu hwv hw _ hm (exists_valid 𝔄 hu).choose_spec.snd.choose_spec ht

#audit_axioms gval_eq

end HL1
end TulenbaevHorrocks
end BooneHigmanLinear
end GroupApproximation
