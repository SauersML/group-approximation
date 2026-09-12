import GroupApproximation.Sofic.AffineHNNBaseRealization
import GroupApproximation.Meta.AxiomGuard

/-!
# Reduction modulo odd integers separates the elements of `V`

`non_mf_groups_exist.tex`, the remark after `prop:max-infinite` (tex lines
765-783 at 73c867c5b):

> … has the faithful matrix realization
> `V ≅ { [[2ᵏ A, v], [0,1]] : A ∈ SL₃(ℤ), v ∈ ℤ[1/2]³, k ∈ ℤ }`,
> and reduction modulo odd integers separates its elements, so `V` is
> residually finite and MF [Korchagin, Corollary 10].

`Sofic/AffineHNNBaseRealization.lean` proves the realization.  The residual
finiteness on main (`MaxInfiniteConverse.residuallyFinite`) separates the
stable-letter exponent by the height homomorphism instead of by reduction.  This
module carries the printed route:

* `dyadicReduceHom m hm : ℤ[1/2] →+* ℤ/m` for odd `m` (`2` is a unit mod `m`),
  `k/2ⁿ ↦ k · 2⁻ⁿ`, well defined on representatives;
* every entry of the realization is dyadic, so reducing entrywise gives
  homomorphisms `reductionHom m hm : V →* GL₄(ℤ/m)`;
* distinct elements of `V` have realizations differing in some entry
  `q ≠ q'`, `q − q' = c/2ⁿ` with `c ≠ 0`, and any odd prime `p > |c|` makes the
  two reductions differ: reduction modulo odd integers separates the elements;
* hence `V` is residually finite, and MF by `lem:rfmf`
  (`isOperatorMF_of_residuallyFinite`, the in-repository proof of the cited
  Korchagin corollary).
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMFSentences

open Matrix ExplicitLinearModel MarkedCompression DyadicRationals AffineHNNBase
open Manuscript.OneSidedMFRadical.MaxInfiniteConverse

noncomputable section

/-! ## Reducing `ℤ[1/2]` modulo an odd integer -/

section Reduction

variable (m : ℕ) (hm : Nat.Coprime 2 m)

/-- The inverse of `2` modulo an odd `m`. -/
def halfMod : ZMod m := ((ZMod.unitOfCoprime 2 hm)⁻¹ : (ZMod m)ˣ)

theorem two_mul_halfMod : (2 : ZMod m) * halfMod m hm = 1 := by
  have h := (ZMod.unitOfCoprime 2 hm).mul_inv
  rw [ZMod.coe_unitOfCoprime] at h
  exact_mod_cast h

/-- The reduction of `k / 2ⁿ` modulo `m`. -/
def repReduce (k : ℤ) (n : ℕ) : ZMod m := (k : ZMod m) * halfMod m hm ^ n

theorem repReduce_eq_of_eq {k k' : ℤ} {n n' : ℕ}
    (h : (k : ℚ) / 2 ^ n = (k' : ℚ) / 2 ^ n') :
    repReduce m hm k n = repReduce m hm k' n' := by
  have h2n : (2 : ℚ) ^ n ≠ 0 := pow_ne_zero _ two_ne_zero
  have h2n' : (2 : ℚ) ^ n' ≠ 0 := pow_ne_zero _ two_ne_zero
  have hz : k * 2 ^ n' = k' * 2 ^ n := by
    rw [div_eq_div_iff h2n h2n'] at h
    exact_mod_cast h
  have hzm : (k : ZMod m) * 2 ^ n' = (k' : ZMod m) * 2 ^ n := by
    have hc := congrArg (Int.cast : ℤ → ZMod m) hz
    push_cast at hc
    exact hc
  have hu := two_mul_halfMod m hm
  unfold repReduce
  calc (k : ZMod m) * halfMod m hm ^ n
      = (k : ZMod m) * halfMod m hm ^ n * ((2 : ZMod m) * halfMod m hm) ^ n' := by
        rw [hu, one_pow, mul_one]
    _ = ((k : ZMod m) * 2 ^ n') * (halfMod m hm ^ n * halfMod m hm ^ n') := by ring
    _ = ((k' : ZMod m) * 2 ^ n) * (halfMod m hm ^ n * halfMod m hm ^ n') := by rw [hzm]
    _ = (k' : ZMod m) * halfMod m hm ^ n' * ((2 : ZMod m) * halfMod m hm) ^ n := by ring
    _ = (k' : ZMod m) * halfMod m hm ^ n' := by rw [hu, one_pow, mul_one]

/-- The reduction of a dyadic rational modulo `m`. -/
def dyadicReduce (x : DyadicRationals.Dyadic) : ZMod m := repReduce m hm (repNum x) (repExp x)

theorem dyadicReduce_of_rep (x : DyadicRationals.Dyadic) {k : ℤ} {n : ℕ}
    (h : (x : ℚ) = (k : ℚ) / 2 ^ n) :
    dyadicReduce m hm x = repReduce m hm k n :=
  repReduce_eq_of_eq m hm ((rep_spec x).symm.trans h)

/-- **Reduction modulo an odd integer**, `ℤ[1/2] →+* ℤ/m`. -/
def dyadicReduceHom : DyadicRationals.Dyadic →+* ZMod m where
  toFun := dyadicReduce m hm
  map_one' := by
    rw [dyadicReduce_of_rep m hm 1 (k := 1) (n := 0) (by simp)]
    simp [repReduce]
  map_mul' x y := by
    obtain ⟨k, n, hx⟩ := exists_rep x
    obtain ⟨l, n', hy⟩ := exists_rep y
    have hxy : ((x * y : DyadicRationals.Dyadic) : ℚ) = ((k * l : ℤ) : ℚ) / 2 ^ (n + n') := by
      rw [Subring.coe_mul, hx, hy, div_mul_div_comm, pow_add]
      norm_cast
    rw [dyadicReduce_of_rep m hm _ hxy, dyadicReduce_of_rep m hm x hx,
      dyadicReduce_of_rep m hm y hy]
    simp only [repReduce]
    push_cast
    ring
  map_zero' := by
    rw [dyadicReduce_of_rep m hm 0 (k := 0) (n := 0) (by simp)]
    simp [repReduce]
  map_add' x y := by
    obtain ⟨k, n, hx⟩ := exists_rep x
    obtain ⟨l, n', hy⟩ := exists_rep y
    have hn : ((2 : ℚ)) ^ n ≠ 0 := pow_ne_zero _ two_ne_zero
    have hn' : ((2 : ℚ)) ^ n' ≠ 0 := pow_ne_zero _ two_ne_zero
    have hxy : ((x + y : DyadicRationals.Dyadic) : ℚ)
        = ((k * 2 ^ n' + 2 ^ n * l : ℤ) : ℚ) / 2 ^ (n + n') := by
      rw [Subring.coe_add, hx, hy, div_add_div _ _ hn hn', pow_add]
      norm_cast
    rw [dyadicReduce_of_rep m hm _ hxy, dyadicReduce_of_rep m hm x hx,
      dyadicReduce_of_rep m hm y hy]
    have hu := two_mul_halfMod m hm
    have key : ∀ a b : ZMod m,
        (a * 2 ^ n' + 2 ^ n * b) * halfMod m hm ^ (n + n')
          = a * halfMod m hm ^ n + b * halfMod m hm ^ n' := by
      intro a b
      calc (a * 2 ^ n' + 2 ^ n * b) * halfMod m hm ^ (n + n')
          = a * halfMod m hm ^ n * ((2 : ZMod m) * halfMod m hm) ^ n'
            + b * halfMod m hm ^ n' * ((2 : ZMod m) * halfMod m hm) ^ n := by ring
        _ = a * halfMod m hm ^ n + b * halfMod m hm ^ n' := by
          rw [hu, one_pow, one_pow, mul_one, mul_one]
    simp only [repReduce]
    push_cast
    exact key _ _

theorem dyadicReduceHom_apply (x : DyadicRationals.Dyadic) :
    dyadicReduceHom m hm x = dyadicReduce m hm x := rfl

end Reduction

/-- **Distinct dyadic rationals have distinct reductions modulo some odd prime.** -/
theorem exists_odd_prime_dyadicReduce_ne {x y : DyadicRationals.Dyadic} (hxy : x ≠ y) :
    ∃ (p : ℕ) (hp : Nat.Coprime 2 p), p.Prime ∧
      dyadicReduceHom p hp x ≠ dyadicReduceHom p hp y := by
  obtain ⟨c, n, hc⟩ := exists_rep (x - y)
  have hc0 : c ≠ 0 := by
    intro h0
    apply hxy
    have hcoe : ((x - y : DyadicRationals.Dyadic) : ℚ) = ((0 : DyadicRationals.Dyadic) : ℚ) := by
      rw [hc, h0]
      simp
    exact sub_eq_zero.mp (Subtype.ext hcoe)
  obtain ⟨p, hple, hp⟩ := Nat.exists_infinite_primes (max 3 (c.natAbs + 1))
  have hp3 : 3 ≤ p := le_trans (le_max_left _ _) hple
  have hcop : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).mpr (by omega)
  haveI : NeZero p := ⟨by omega⟩
  refine ⟨p, hcop, hp, fun heq ↦ ?_⟩
  have hsub : dyadicReduceHom p hcop (x - y) = 0 := by
    rw [map_sub (dyadicReduceHom p hcop) x y, heq, sub_self]
  rw [dyadicReduceHom_apply, dyadicReduce_of_rep p hcop (x - y) hc, repReduce] at hsub
  have hu := two_mul_halfMod p hcop
  have hcz : (c : ZMod p) = 0 := by
    calc (c : ZMod p) = (c : ZMod p) * halfMod p hcop ^ n * 2 ^ n := by
          rw [mul_assoc, ← mul_pow, mul_comm (halfMod p hcop), hu, one_pow, mul_one]
      _ = 0 := by rw [hsub, zero_mul]
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hcz
  have hle : (p : ℤ) ≤ |c| := Int.le_of_dvd (abs_pos.mpr hc0) ((dvd_abs _ _).mpr hcz)
  have hlt : (c.natAbs : ℤ) < (p : ℤ) := by
    have hh : c.natAbs + 1 ≤ p := le_trans (le_max_right _ _) hple
    exact_mod_cast Nat.lt_of_succ_le hh
  rw [Int.abs_eq_natAbs] at hle
  omega

/-! ## The realization has dyadic entries -/

theorem two_zpow_mem_dyadicSubring (k : ℤ) : ((2 : ℚ) ^ k) ∈ dyadicSubring := by
  rcases Int.eq_nat_or_neg k with ⟨n, rfl | rfl⟩
  · exact mem_dyadicSubring.mpr ⟨2 ^ n, 0, by simp⟩
  · exact mem_dyadicSubring.mpr ⟨1, n, by simp [_root_.zpow_neg]⟩

set_option linter.unusedSimpArgs false in
theorem realization_entry_mem_dyadicSubring (v : V) (i j : Fin 4) :
    ((realization v : Matˣ) : Mat) i j ∈ dyadicSubring := by
  obtain ⟨k, A, w, hw, hval⟩ := realization_mem_printed v
  rw [hval]
  fin_cases i <;> fin_cases j <;>
    simp [printedMat, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] <;>
    first
      | exact mul_mem (two_zpow_mem_dyadicSubring k) (intCast_mem dyadicSubring _)
      | exact hw _

/-- The realization of `v`, read as a matrix over `ℤ[1/2]`. -/
def dyadicMat (v : V) : Matrix (Fin 4) (Fin 4) DyadicRationals.Dyadic :=
  fun i j ↦ ⟨((realization v : Matˣ) : Mat) i j, realization_entry_mem_dyadicSubring v i j⟩

theorem dyadicMat_mul (v w : V) : dyadicMat (v * w) = dyadicMat v * dyadicMat w := by
  apply Matrix.map_injective (f := (dyadicSubring.subtype : DyadicRationals.Dyadic → ℚ))
    Subtype.val_injective
  change (dyadicMat (v * w)).map dyadicSubring.subtype
    = (dyadicMat v * dyadicMat w).map dyadicSubring.subtype
  rw [Matrix.map_mul]
  change ((realization (v * w) : Matˣ) : Mat)
    = ((realization v : Matˣ) : Mat) * ((realization w : Matˣ) : Mat)
  rw [map_mul realization v w, Units.val_mul]

theorem dyadicMat_one : dyadicMat 1 = 1 := by
  apply Matrix.map_injective (f := (dyadicSubring.subtype : DyadicRationals.Dyadic → ℚ))
    Subtype.val_injective
  change (dyadicMat 1).map dyadicSubring.subtype
    = (1 : Matrix (Fin 4) (Fin 4) DyadicRationals.Dyadic).map dyadicSubring.subtype
  rw [Matrix.map_one _ (map_zero dyadicSubring.subtype) (map_one dyadicSubring.subtype)]
  change ((realization 1 : Matˣ) : Mat) = 1
  rw [map_one realization, Units.val_one]

/-! ## Reduction homomorphisms of `V` -/

/-- **Reduction modulo an odd integer** of the realization, `V →* GL₄(ℤ/m)`. -/
def reductionHom (m : ℕ) (hm : Nat.Coprime 2 m) :
    V →* (Matrix (Fin 4) (Fin 4) (ZMod m))ˣ where
  toFun v :=
    ⟨(dyadicMat v).map (dyadicReduceHom m hm), (dyadicMat v⁻¹).map (dyadicReduceHom m hm),
      by rw [← Matrix.map_mul, ← dyadicMat_mul, mul_inv_cancel, dyadicMat_one,
        Matrix.map_one _ (map_zero _) (map_one _)],
      by rw [← Matrix.map_mul, ← dyadicMat_mul, inv_mul_cancel, dyadicMat_one,
        Matrix.map_one _ (map_zero _) (map_one _)]⟩
  map_one' := by
    apply Units.ext
    change (dyadicMat 1).map (dyadicReduceHom m hm) = 1
    rw [dyadicMat_one, Matrix.map_one _ (map_zero _) (map_one _)]
  map_mul' v w := by
    apply Units.ext
    change (dyadicMat (v * w)).map (dyadicReduceHom m hm)
      = (dyadicMat v).map (dyadicReduceHom m hm) * (dyadicMat w).map (dyadicReduceHom m hm)
    rw [dyadicMat_mul, Matrix.map_mul]

theorem reductionHom_apply (m : ℕ) (hm : Nat.Coprime 2 m) (v : V) (i j : Fin 4) :
    ((reductionHom m hm v : (Matrix (Fin 4) (Fin 4) (ZMod m))ˣ) :
        Matrix (Fin 4) (Fin 4) (ZMod m)) i j
      = dyadicReduceHom m hm
          ⟨((realization v : Matˣ) : Mat) i j, realization_entry_mem_dyadicSubring v i j⟩ :=
  rfl

/-- **The printed separation**: reduction modulo odd integers separates the
elements of `V`. -/
theorem manuscriptSentence_reductionModuloOddSeparates (v w : V) (hvw : v ≠ w) :
    ∃ (m : ℕ) (hm : Nat.Coprime 2 m), reductionHom m hm v ≠ reductionHom m hm w := by
  have hne : ((realization v : Matˣ) : Mat) ≠ ((realization w : Matˣ) : Mat) :=
    fun h ↦ hvw (realization_injective (Units.ext h))
  obtain ⟨i, j, hij⟩ :
      ∃ i j, ((realization v : Matˣ) : Mat) i j ≠ ((realization w : Matˣ) : Mat) i j := by
    by_contra hcon
    push Not at hcon
    exact hne (Matrix.ext hcon)
  have hdy : dyadicMat v i j ≠ dyadicMat w i j :=
    fun (h : dyadicMat v i j = dyadicMat w i j) ↦ hij (congrArg Subtype.val h)
  obtain ⟨p, hp, -, hred⟩ := exists_odd_prime_dyadicReduce_ne hdy
  refine ⟨p, hp, fun heq ↦ hred ?_⟩
  exact congrArg
    (fun u : (Matrix (Fin 4) (Fin 4) (ZMod p))ˣ ↦ (u : Matrix (Fin 4) (Fin 4) (ZMod p)) i j) heq

/-- **`V` is residually finite**, by the reduction homomorphisms. -/
theorem residuallyFinite_of_reductionModuloOdd : Group.ResiduallyFinite V := by
  refine Group.residuallyFinite_of_forall_exists_finite_monoidHom.{0} ?_
  intro v hv
  obtain ⟨m, hm, hne⟩ := manuscriptSentence_reductionModuloOddSeparates v 1 hv
  refine ⟨(Matrix (Fin 4) (Fin 4) (ZMod m))ˣ, inferInstance, ?_, reductionHom m hm, ?_⟩
  · haveI : NeZero m := ⟨by
      rintro rfl
      simp [Nat.Coprime] at hm⟩
    infer_instance
  · rwa [map_one (reductionHom m hm)] at hne

/-- **The printed clause, every part**: the reductions modulo odd integers are
homomorphisms given entrywise by reducing the dyadic realization, they separate
the elements of `V`, and `V` is residually finite and MF. -/
def PrintedReductionModuloOddSeparates : Prop :=
  (∀ v w : V, v ≠ w → ∃ (m : ℕ) (hm : Nat.Coprime 2 m),
      reductionHom m hm v ≠ reductionHom m hm w) ∧
    Group.ResiduallyFinite V ∧ IsOperatorMF V

theorem manuscriptSentence_reductionModuloOddRFAndMF :
    PrintedReductionModuloOddSeparates := by
  refine ⟨manuscriptSentence_reductionModuloOddSeparates,
    residuallyFinite_of_reductionModuloOdd, ?_⟩
  haveI := residuallyFinite_of_reductionModuloOdd
  exact isOperatorMF_of_residuallyFinite

end

end NonMFSentences
end Manuscript
end GroupApproximation

open GroupApproximation

#audit_axioms
  Manuscript.NonMFSentences.manuscriptSentence_reductionModuloOddSeparates
#audit_closed_axioms
  Manuscript.NonMFSentences.manuscriptSentence_reductionModuloOddRFAndMF
