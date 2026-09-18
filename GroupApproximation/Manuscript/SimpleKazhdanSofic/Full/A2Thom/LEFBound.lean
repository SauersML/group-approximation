import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Finiteness.Cardinality
import GroupApproximation.Meta.AxiomGuard

/-!
# Evaluating Laurent polynomials at a root of unity (Thom, Lemma 2.3, arithmetic part)

`simple_kazhdan_sofic_group.tex`, Introduction, tex l.57–59 (table row A2): Thom's group is
"locally embeddable into finite groups". Thom (Groups Geom. Dyn. 4 (2010), §2.1, Lemma 2.3)
reduces `F_p[t,t⁻¹]` to the finite ring `F_p[ℤ/M]` for large `M`. This file has the ring-level
facts that proof needs.

* `LaurentBound N p`: `p` is supported in degrees `[-N, N]`. Every Laurent polynomial is bounded
  (`exists_laurentBound`), and bounds are stable under `+`, `-` and enlarging `N`.
* `CycRing K m = K[X]/(X^{m+1} - 1)`, which is finite when `K` is finite (`cycRing_finite`), and
  `cycEval K m : K[t,t⁻¹] →+* CycRing K m` sends `t` to the class of `X`.
* `LaurentBound.eq_of_cycEval_eq`: if `2N ≤ m`, then `cycEval K m` is injective on Laurent
  polynomials bounded by `N`.
-/

namespace GroupApproximation.Full.A2Thom

open Polynomial

section Bound

variable {K : Type*} [CommRing K]

/-- `p` is supported in degrees `[-N, N]`: `p · t^N` is a polynomial of degree at most `2N`. -/
def LaurentBound (N : ℕ) (p : LaurentPolynomial K) : Prop :=
  ∃ q : K[X], Polynomial.toLaurent q = p * LaurentPolynomial.T (N : ℤ) ∧ q.natDegree ≤ 2 * N

theorem laurentBound_of {N n : ℕ} {p : LaurentPolynomial K} {q : K[X]}
    (hq : Polynomial.toLaurent q = p * LaurentPolynomial.T (n : ℤ)) (hn : n ≤ N)
    (hd : q.natDegree + (N - n) ≤ 2 * N) : LaurentBound N p := by
  refine ⟨q * Polynomial.X ^ (N - n), ?_, ?_⟩
  · have hcast : ((n : ℕ) : ℤ) + ((N - n : ℕ) : ℤ) = (N : ℤ) := by
      rw [Nat.cast_sub hn]
      ring
    rw [map_mul, Polynomial.toLaurent_X_pow, hq, LaurentPolynomial.mul_T_assoc, hcast]
  · calc (q * Polynomial.X ^ (N - n)).natDegree
        ≤ q.natDegree + (Polynomial.X ^ (N - n) : K[X]).natDegree :=
          Polynomial.natDegree_mul_le
      _ ≤ q.natDegree + (N - n) :=
          Nat.add_le_add_left (Polynomial.natDegree_X_pow_le (N - n)) _
      _ ≤ 2 * N := hd

theorem LaurentBound.mono {N N' : ℕ} {p : LaurentPolynomial K} (h : LaurentBound N p)
    (hN : N ≤ N') : LaurentBound N' p := by
  obtain ⟨q, hq, hd⟩ := h
  exact laurentBound_of hq hN (by omega)

theorem exists_laurentBound (p : LaurentPolynomial K) : ∃ N, LaurentBound N p := by
  obtain ⟨n, q, hq⟩ := LaurentPolynomial.exists_T_pow p
  exact ⟨n + q.natDegree, laurentBound_of hq (Nat.le_add_right n _) (by omega)⟩

theorem laurentBound_zero (N : ℕ) : LaurentBound N (0 : LaurentPolynomial K) := by
  refine ⟨0, ?_, ?_⟩
  · rw [map_zero, zero_mul]
  · rw [Polynomial.natDegree_zero]
    exact Nat.zero_le _

theorem laurentBound_one (N : ℕ) : LaurentBound N (1 : LaurentPolynomial K) := by
  refine ⟨Polynomial.X ^ N, ?_, ?_⟩
  · rw [Polynomial.toLaurent_X_pow, one_mul]
  · have h := Polynomial.natDegree_X_pow_le (R := K) N
    omega

theorem laurentBound_toLaurent {N : ℕ} (r : K[X]) (hr : r.natDegree ≤ N) :
    LaurentBound N (Polynomial.toLaurent r) := by
  refine ⟨r * Polynomial.X ^ N, ?_, ?_⟩
  · rw [map_mul, Polynomial.toLaurent_X_pow]
  · have h1 : (r * Polynomial.X ^ N).natDegree ≤ r.natDegree + (Polynomial.X ^ N : K[X]).natDegree :=
      Polynomial.natDegree_mul_le
    have h2 := Polynomial.natDegree_X_pow_le (R := K) N
    omega

theorem LaurentBound.add {N : ℕ} {p p' : LaurentPolynomial K} (h : LaurentBound N p)
    (h' : LaurentBound N p') : LaurentBound N (p + p') := by
  obtain ⟨q, hq, hd⟩ := h
  obtain ⟨q', hq', hd'⟩ := h'
  refine ⟨q + q', ?_, ?_⟩
  · rw [map_add, hq, hq', add_mul]
  · exact (Polynomial.natDegree_add_le q q').trans (max_le hd hd')

theorem LaurentBound.sub {N : ℕ} {p p' : LaurentPolynomial K} (h : LaurentBound N p)
    (h' : LaurentBound N p') : LaurentBound N (p - p') := by
  obtain ⟨q, hq, hd⟩ := h
  obtain ⟨q', hq', hd'⟩ := h'
  refine ⟨q - q', ?_, ?_⟩
  · rw [map_sub, hq, hq', sub_mul]
  · exact (Polynomial.natDegree_sub_le q q').trans (max_le hd hd')

end Bound

section Cyc

variable (K : Type*) [CommRing K]

/-- `X^{m+1} - 1`. -/
noncomputable def cycPoly (m : ℕ) : K[X] :=
  Polynomial.X ^ (m + 1) - Polynomial.C 1

theorem cycPoly_monic (m : ℕ) : (cycPoly K m).Monic :=
  Polynomial.monic_X_pow_sub_C 1 (Nat.succ_ne_zero m)

theorem natDegree_cycPoly [Nontrivial K] (m : ℕ) : (cycPoly K m).natDegree = m + 1 := by
  show (Polynomial.X ^ (m + 1) - Polynomial.C 1 : K[X]).natDegree = m + 1
  exact Polynomial.natDegree_X_pow_sub_C

/-- The finite ring `K[ℤ/(m+1)] = K[X]/(X^{m+1} - 1)` (Thom, Lemma 2.3). -/
abbrev CycRing (m : ℕ) : Type _ :=
  AdjoinRoot (cycPoly K m)

theorem cyc_root_pow (m : ℕ) : AdjoinRoot.root (cycPoly K m) ^ (m + 1) = 1 := by
  calc AdjoinRoot.root (cycPoly K m) ^ (m + 1)
      = AdjoinRoot.mk (cycPoly K m) (Polynomial.X ^ (m + 1)) := by
        rw [map_pow, AdjoinRoot.mk_X]
    _ = AdjoinRoot.mk (cycPoly K m) 1 :=
        AdjoinRoot.mk_eq_mk.2 ⟨1, by rw [mul_one, cycPoly, Polynomial.C_1]⟩
    _ = 1 := map_one _

/-- The class of `X` is a unit of `CycRing K m`, with inverse `X^m`. -/
noncomputable def cycUnit (m : ℕ) : (CycRing K m)ˣ where
  val := AdjoinRoot.root (cycPoly K m)
  inv := AdjoinRoot.root (cycPoly K m) ^ m
  val_inv := by rw [← pow_succ', cyc_root_pow]
  inv_val := by rw [← pow_succ, cyc_root_pow]

/-- `t ↦ X`: the evaluation `K[t,t⁻¹] → K[X]/(X^{m+1} - 1)`. -/
noncomputable def cycEval (m : ℕ) : LaurentPolynomial K →+* CycRing K m :=
  LaurentPolynomial.eval₂ (AdjoinRoot.of (cycPoly K m)) (cycUnit K m)

theorem cycEval_toLaurent (m : ℕ) (q : K[X]) :
    cycEval K m (Polynomial.toLaurent q) = AdjoinRoot.mk (cycPoly K m) q := by
  have hu : ((cycUnit K m : (CycRing K m)ˣ) : CycRing K m) = AdjoinRoot.root (cycPoly K m) :=
    rfl
  rw [cycEval, LaurentPolynomial.eval₂_toLaurent, hu, ← AdjoinRoot.algebraMap_eq,
    ← Polynomial.aeval_def, AdjoinRoot.aeval_eq]

instance cycRing_finite [Finite K] (m : ℕ) : Finite (CycRing K m) :=
  haveI : Module.Finite K (CycRing K m) := (cycPoly_monic K m).finite_adjoinRoot
  Module.finite_of_finite K

end Cyc

section Injective

variable {K : Type*} [CommRing K] [Nontrivial K]

/-- A Laurent polynomial supported in `[-N, N]` that vanishes in `K[X]/(X^{m+1} - 1)`, where
`2N ≤ m`, is zero. -/
theorem LaurentBound.eq_zero_of_cycEval {N m : ℕ} {p : LaurentPolynomial K}
    (hp : LaurentBound N p) (hm : 2 * N ≤ m) (h : cycEval K m p = 0) : p = 0 := by
  obtain ⟨q, hq, hd⟩ := hp
  have hq0 : q = 0 := by
    by_contra hq0
    refine AdjoinRoot.mk_ne_zero_of_natDegree_lt (cycPoly_monic K m) hq0 ?_ ?_
    · rw [natDegree_cycPoly]
      omega
    · rw [← cycEval_toLaurent, hq, map_mul, h, zero_mul]
  have hT : p * LaurentPolynomial.T (N : ℤ) = 0 := by
    rw [← hq, hq0, map_zero]
  calc p = p * LaurentPolynomial.T (N : ℤ) * LaurentPolynomial.T (-(N : ℤ)) := by
        rw [LaurentPolynomial.mul_T_assoc, add_neg_cancel, LaurentPolynomial.T_zero, mul_one]
    _ = 0 := by rw [hT, zero_mul]

/-- `cycEval K m` is injective on Laurent polynomials supported in `[-N, N]` when `2N ≤ m`
(Thom, Lemma 2.3). -/
theorem LaurentBound.eq_of_cycEval_eq {N m : ℕ} {p p' : LaurentPolynomial K}
    (hp : LaurentBound N p) (hp' : LaurentBound N p') (hm : 2 * N ≤ m)
    (h : cycEval K m p = cycEval K m p') : p = p' :=
  sub_eq_zero.1 ((hp.sub hp').eq_zero_of_cycEval hm (by rw [map_sub, h, sub_self]))

end Injective

#audit_axioms GroupApproximation.Full.A2Thom.LaurentBound.eq_of_cycEval_eq

end GroupApproximation.Full.A2Thom
