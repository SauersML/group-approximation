import GroupApproximation.BooneHigman.Metabelian.VdKSRStep
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Ideal.Prime
import Mathlib.Order.KrullDimension
import GroupApproximation.Meta.AxiomGuard

/-!
# Heitmann's bound `sr(R) ≤ dim R + 1` from Mathlib's Krull dimension

Lane `fix-bh-a`.  Lane `bh-met-90m` proved stable range from the Coquand–Lombardi elementary
dimension: `vdkSR_KdimLE I n` ("every `n`-tuple has a collapse in `I`", `VdKSRCollapse`) and
`vdkSR_stableRangeLE_of_kdimLE` (`VdKSRStep`).  This file bridges the classical dimension
`ringKrullDim` (chains of primes) to that elementary one.

* `ChainLT I n`: every chain of primes `P₀ < ⋯ < P_ℓ` with `I ≤ P₀` has `ℓ < n`, i.e.
  `dim V(I) < n`.
* `exists_lt_of_bdry_le`: a prime `Q` containing the boundary ideal `vdkSR_bdry I y` contains `y`
  and `(I : y^∞)`.  So the monoid `(R ∖ Q) · y^ℕ` misses `I`, and a prime `P ⊇ I` disjoint from it
  satisfies `P < Q` (`Ideal.exists_le_prime_disjoint`).
* `chainLT_bdry`: hence `ChainLT I (n + 1) → ChainLT (vdkSR_bdry I y) n`.
* `kdimLE_of_chainLT`: `ChainLT I n → vdkSR_KdimLE I n`, by induction on `n`.  The case `n + 1`
  unfolds one collapse against the boundary ideal.
* `stableRangeLE_of_ringKrullDim_le`: **`ringKrullDim R ≤ d → sr(R) ≤ d + 1`** for every
  commutative ring `R`.  This is Heitmann's theorem; no noetherian hypothesis is needed.
-/

namespace GroupApproximation.StableRange

open GroupApproximation.BooneHigman.Metabelian.ElemFP

variable {R : Type*} [CommRing R]

/-- `dim V(I) < n`: every chain of primes whose bottom contains `I` has length `< n`. -/
def ChainLT (I : Ideal R) (n : ℕ) : Prop :=
  ∀ s : LTSeries (PrimeSpectrum R), I ≤ s.head.asIdeal → s.length < n

#audit_axioms GroupApproximation.StableRange.ChainLT

/-- `dim V(I) < 0` forces `I = ⊤`. -/
theorem eq_top_of_chainLT_zero {I : Ideal R} (h : ChainLT I 0) : I = ⊤ := by
  by_contra hI
  obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I hI
  exact Nat.not_lt_zero _ (h (RelSeries.singleton _ ⟨M, hM.isPrime⟩) hIM)

#audit_axioms GroupApproximation.StableRange.eq_top_of_chainLT_zero

/-- A prime containing the boundary ideal `vdkSR_bdry I y` lies strictly above a prime containing
`I`. -/
theorem exists_lt_of_bdry_le {I : Ideal R} {y : R} (Q : PrimeSpectrum R)
    (hQ : vdkSR_bdry I y ≤ Q.asIdeal) : ∃ P : PrimeSpectrum R, I ≤ P.asIdeal ∧ P < Q := by
  have hyQ : y ∈ Q.asIdeal := hQ (vdkSR_mem_bdry.mpr ⟨1, 0, by simp⟩)
  have hdisj : Disjoint (I : Set R)
      ((Q.asIdeal.primeCompl ⊔ Submonoid.powers y : Submonoid R) : Set R) := by
    refine Set.disjoint_left.mpr fun x hxI hxS => ?_
    obtain ⟨a, ha, b, hb, rfl⟩ := Submonoid.mem_sup.mp (SetLike.mem_coe.mp hxS)
    obtain ⟨k, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp hb
    refine Ideal.mem_primeCompl_iff.mp ha (hQ (vdkSR_mem_bdry.mpr ⟨0, k, ?_⟩))
    rw [mul_zero, sub_zero, mul_comm]
    exact SetLike.mem_coe.mp hxI
  obtain ⟨P, hP, hIP, hPS⟩ := Ideal.exists_le_prime_disjoint (I := I) _ hdisj
  have hPQ : P ≤ Q.asIdeal := fun x hxP => by
    by_contra hxQ
    exact Set.disjoint_left.mp hPS (SetLike.mem_coe.mpr hxP)
      (SetLike.mem_coe.mpr (Submonoid.mem_sup_left (Ideal.mem_primeCompl_iff.mpr hxQ)))
  have hyP : y ∉ P := fun hyP =>
    Set.disjoint_left.mp hPS (SetLike.mem_coe.mpr hyP)
      (SetLike.mem_coe.mpr (Submonoid.mem_sup_right (Submonoid.mem_powers y)))
  have hlt : P < Q.asIdeal := lt_of_le_of_ne hPQ (ne_of_mem_of_not_mem' hyQ hyP).symm
  exact ⟨⟨P, hP⟩, hIP, (PrimeSpectrum.asIdeal_lt_asIdeal ⟨P, hP⟩ Q).mp hlt⟩

#audit_axioms GroupApproximation.StableRange.exists_lt_of_bdry_le

/-- Passing to the boundary ideal lowers the classical dimension bound by one. -/
theorem chainLT_bdry {I : Ideal R} {n : ℕ} (h : ChainLT I (n + 1)) (y : R) :
    ChainLT (vdkSR_bdry I y) n := by
  intro s hs
  obtain ⟨P, hIP, hPQ⟩ := exists_lt_of_bdry_le s.head hs
  have h1 := h (s.cons P hPQ) (by simpa using hIP)
  simp only [RelSeries.cons_length] at h1
  omega

#audit_axioms GroupApproximation.StableRange.chainLT_bdry

/-- **Classical dimension bounds elementary dimension**: `dim V(I) < n` gives
`vdkSR_KdimLE I n`. -/
theorem kdimLE_of_chainLT : ∀ (n : ℕ) (I : Ideal R), ChainLT I n → vdkSR_KdimLE I n
  | 0, I, h => by
    intro x
    refine ⟨x, fun _ => 0, ?_⟩
    rw [vdkSR_collapse_zero, eq_top_of_chainLT_zero h]
    exact Submodule.mem_top
  | n + 1, I, h => by
    intro x
    obtain ⟨a, m, ha⟩ := kdimLE_of_chainLT n _ (chainLT_bdry h (x 0)) (Fin.tail x)
    obtain ⟨t, k, ht⟩ := vdkSR_mem_bdry.mp ha
    refine ⟨Fin.cons (-t) a, Fin.cons k m, ?_⟩
    rw [vdkSR_collapse_succ]
    simp only [Fin.tail_cons, Fin.cons_zero]
    have e : x 0 ^ k * (vdkSR_collapse n (Fin.tail x) a m + -t * x 0) =
        x 0 ^ k * (vdkSR_collapse n (Fin.tail x) a m - x 0 * t) := by ring
    rw [e]
    exact ht

#audit_axioms GroupApproximation.StableRange.kdimLE_of_chainLT

/-- `ringKrullDim R ≤ d` bounds the length of every chain of primes by `d`. -/
theorem chainLT_bot_of_ringKrullDim_le {d : ℕ} (hd : ringKrullDim R ≤ d) {n : ℕ}
    (hn : d + 1 ≤ n) : ChainLT (⊥ : Ideal R) n := by
  intro s _
  have h1 : (s.length : WithBot ℕ∞) ≤ d := (Order.LTSeries.length_le_krullDim s).trans hd
  have h2 : s.length ≤ d := by exact_mod_cast h1
  omega

#audit_axioms GroupApproximation.StableRange.chainLT_bot_of_ringKrullDim_le

/-- **Heitmann's bound**: a commutative ring of Krull dimension `≤ d` has stable range `≤ d + 1`
(Bass's condition `vdkStab_StableRangeLE`). -/
theorem stableRangeLE_of_ringKrullDim_le {d : ℕ} (hd : ringKrullDim R ≤ d) :
    vdkStab_StableRangeLE R (d + 1) :=
  vdkSR_stableRangeLE_of_kdimLE (d + 1) fun n hn =>
    kdimLE_of_chainLT n ⊥ (chainLT_bot_of_ringKrullDim_le hd hn)

#audit_axioms GroupApproximation.StableRange.stableRangeLE_of_ringKrullDim_le

end GroupApproximation.StableRange
