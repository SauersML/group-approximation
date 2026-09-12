import GroupApproximation.CharClass.LIXKMap
import GroupApproximation.CharClass.LIXShapeGeneric
import GroupApproximation.Meta.AxiomGuard

/-!
# The `k`-fold map `Ψ_k` on `ℂ^{n+1}`, its `k+1` preimages of `−e₀`, and the rotation

Lane `sp-oddside-n` of the STW Problem LIX strengthening
(`notes/LIX_STRONGER_PROGRAM_2026-09-10.md` §1.3.2; report
`notes/lix-stronger-lane-reports/sp-oddside-n.md` §0.3 file C).

`CharClass/LIXKMap.lean` is `sp-oddside`'s rank-two version of this file.  Everything in it
that is about `ℂ` rather than about `ℂ³` is reused here and **not** restated: `kUnity`,
`kBase`, `kRoot`, `kRoot_pow`, `norm_kRoot`, `kRoot_injective`,
`exists_kRoot_of_pow_eq_neg_one`, `joinC_eq_pow_of_norm_one`, `joinC_eq_neg_one_iff`,
`joinC_kUnity_pow_mul` and the three `norm_eq_one_of_*` lemmas are statements about
complex numbers and about `Fin (k+1)`, with no sphere in them.  What carries the rank is
five definitions and four proofs, and they are what this file re-authors.

## Why the constant section is at index `0` and not at `Fin.last n`

`sp-tower`'s `CharClass.Gen.eLast n = Pi.single (Fin.last n) 1` is the right constant
section for the one-zero tower: it is the pole around which the analysis side's Householder
frames are built.  The `k`-zero geometry cannot use it.  The clutching coordinate at rank
`n` is `Re (x (Fin.last n))`, so `±e_last` are the suspension points; a hemisphere
preserving self-map of `S^{2n+1}` is a **cone** at a suspension point, and a cone is not a
local homeomorphism.  With `e₀ = Pi.single 0 1` the antipode `−e₀` lies on the equator
(`re_neg_eZero_last`, which needs `0 < n` and nothing else), and `Ψ_k^{-1}(−e₀)` is the
free `ρ`-orbit of `k+1` points below.  The permutation between `e₀` and `e_last` is
absorbed on the Step A side (`sp-design` §1.3), and in this file it is the binder `hGe`.

**`0 < n` is carried on the theorems that need it and on no definition.**

## Main results

* `KGen.eZero`, `KGen.negEZero` — the constant section and its antipode, on the equator.
* `KGen.psiVec` — the map, with norm preservation, continuity, and `Ψ_0 = id`.
* `KGen.kZeroVec`, `KGen.kZero`, `KGen.kZero_injective` — the `k+1` zeros as points of
  `S^{2n+1}`.
* `KGen.psiVec_eq_neg_eZero_iff` — **the zero locus**, at every rank.
* `KGen.psiVec_kRot`, `KGen.kRot_kZeroVec_zero` — the rotation and the free orbit.
* §8 — the four `n = 2` bridges to `sp-oddside`'s names, every one `rfl`.
-/

noncomputable section

namespace GroupApproximation.CharClass

namespace KGen

open GroupApproximation.STW59
open GroupApproximation.LIX.Powers

set_option linter.unusedSectionVars false

/-! ## 1. The constant section at index `0` -/

/-- `e₀`, the strengthened programme's constant section of the trivial block at rank `n`.
Unlike `Gen.eLast n` it is not a suspension point of the clutching coordinate. -/
def eZero (n : ℕ) : Fin (n + 1) → ℂ := Pi.single 0 1

@[simp] theorem eZero_apply_zero (n : ℕ) : eZero n 0 = 1 := Pi.single_eq_same _ _

theorem eZero_apply_of_ne (n : ℕ) {i : Fin (n + 1)} (hi : i ≠ 0) : eZero n i = 0 :=
  Pi.single_eq_of_ne hi _

theorem eZero_normSq (n : ℕ) : ∑ i, ‖eZero n i‖ ^ 2 = 1 := by
  rw [Finset.sum_eq_single (0 : Fin (n + 1))]
  · rw [eZero_apply_zero]
    simp
  · intro b _ hb
    rw [eZero_apply_of_ne n hb]
    simp
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem eZero_ne_zero (n : ℕ) : eZero n ≠ 0 := by
  intro h
  have h0 : eZero n 0 = 0 := by rw [h]; rfl
  rw [eZero_apply_zero] at h0
  exact one_ne_zero h0

/-- The clutching coordinate is the last one, and at positive rank the index `0` is not
the last index.  This one-line fact is the whole reason the constant section may move. -/
theorem last_ne_zero (n : ℕ) (hn : 0 < n) : (Fin.last n) ≠ (0 : Fin (n + 1)) := by
  intro h
  have hv : ((Fin.last n : Fin (n + 1)) : ℕ) = ((0 : Fin (n + 1)) : ℕ) := by rw [h]
  rw [Fin.val_last, Fin.val_zero] at hv
  omega

/-- **`−e₀` is on the equator** `{Re (x (Fin.last n)) = 0}`, at every positive rank. -/
theorem re_neg_eZero_last (n : ℕ) (hn : 0 < n) : ((-eZero n) (Fin.last n)).re = 0 := by
  rw [Pi.neg_apply, eZero_apply_of_ne n (last_ne_zero n hn)]
  simp

/-- The point of `S^{2n+1}` antipodal to `e₀`.  At `k = 0` this is the single zero. -/
def negEZero (n : ℕ) : ↥(unitVectors (Fin (n + 1))) :=
  ⟨fun i => -eZero n i, by
    rw [mem_unitVectors_iff]
    simpa using eZero_normSq n⟩

/-! ## 2. The map `Ψ_k` on `ℂ^{n+1}` -/

/-- **The `k`-fold map at rank `n`**: apply `sp-powers`' scalar join power to the first
coordinate and leave the other `n` alone.  It preserves every coordinate's modulus, hence
the Hermitian norm *and* the equator `{Re (x (Fin.last n)) = 0}`.  The index is
`sp-powers`' shifted one, so `psiVec n k` is the map of degree `k + 1` and `k = 0` is the
identity. -/
def psiVec (n k : ℕ) (x : Fin (n + 1) → ℂ) : Fin (n + 1) → ℂ :=
  Function.update x 0 (joinC k (x 0))

@[simp] theorem psiVec_apply_zero (n k : ℕ) (x : Fin (n + 1) → ℂ) :
    psiVec n k x 0 = joinC k (x 0) :=
  Function.update_self _ _ _

theorem psiVec_apply_of_ne (n k : ℕ) (x : Fin (n + 1) → ℂ) {i : Fin (n + 1)} (hi : i ≠ 0) :
    psiVec n k x i = x i :=
  Function.update_of_ne hi _ _

/-- **`Ψ_k` preserves every coordinate's modulus.** -/
theorem norm_psiVec_apply (n k : ℕ) (x : Fin (n + 1) → ℂ) (i : Fin (n + 1)) :
    ‖psiVec n k x i‖ = ‖x i‖ := by
  rcases eq_or_ne i 0 with rfl | hi
  · rw [psiVec_apply_zero, norm_joinC]
  · rw [psiVec_apply_of_ne n k x hi]

theorem normSq_psiVec (n k : ℕ) (x : Fin (n + 1) → ℂ) :
    ∑ i, ‖psiVec n k x i‖ ^ 2 = ∑ i, ‖x i‖ ^ 2 :=
  Finset.sum_congr rfl fun i _ => by rw [norm_psiVec_apply]

theorem psiVec_mem_unitVectors {n k : ℕ} {x : Fin (n + 1) → ℂ}
    (hx : x ∈ unitVectors (Fin (n + 1))) : psiVec n k x ∈ unitVectors (Fin (n + 1)) := by
  rw [mem_unitVectors_iff, normSq_psiVec]
  exact mem_unitVectors_iff.mp hx

theorem continuous_psiVec (n k : ℕ) : Continuous (psiVec n k) := by
  refine continuous_pi fun i => ?_
  rcases eq_or_ne i 0 with rfl | hi
  · simp only [psiVec_apply_zero]
    exact (continuous_joinC k).comp' (continuous_apply 0)
  · simp only [psiVec_apply_of_ne _ _ _ hi]
    exact continuous_apply i

/-- The clutching coordinate is untouched, so `Ψ_k` is its own suspension: the map of
`S^{2n+1}` and the map of the equator `S^{2n}` are the same formula. -/
theorem psiVec_apply_last (n k : ℕ) (hn : 0 < n) (x : Fin (n + 1) → ℂ) :
    psiVec n k x (Fin.last n) = x (Fin.last n) :=
  psiVec_apply_of_ne n k x (last_ne_zero n hn)

/-- At `k = 0` the map is the identity, so the one-zero geometry is the `k = 0` case of
the `k`-zero geometry and nothing is duplicated. -/
theorem psiVec_zero_eq (n : ℕ) (x : Fin (n + 1) → ℂ) : psiVec n 0 x = x := by
  funext i
  rcases eq_or_ne i 0 with rfl | hi
  · rw [psiVec_apply_zero, joinC_id]
  · rw [psiVec_apply_of_ne _ _ _ hi]

/-! ## 3. The `k+1` zeros, as points of `S^{2n+1}` -/

/-- The `j`-th zero, as a vector: `ζ_j · e₀`.  The scalars `kRoot k j` are `sp-oddside`'s
and are rank-free. -/
def kZeroVec (n k : ℕ) (j : Fin (k + 1)) : Fin (n + 1) → ℂ := Pi.single 0 (kRoot k j)

@[simp] theorem kZeroVec_apply_zero (n k : ℕ) (j : Fin (k + 1)) :
    kZeroVec n k j 0 = kRoot k j :=
  Pi.single_eq_same _ _

theorem kZeroVec_apply_of_ne (n k : ℕ) (j : Fin (k + 1)) {i : Fin (n + 1)} (hi : i ≠ 0) :
    kZeroVec n k j i = 0 :=
  Pi.single_eq_of_ne hi _

theorem kZeroVec_mem (n k : ℕ) (j : Fin (k + 1)) :
    kZeroVec n k j ∈ unitVectors (Fin (n + 1)) := by
  rw [mem_unitVectors_iff, Finset.sum_eq_single (0 : Fin (n + 1))]
  · rw [kZeroVec_apply_zero, norm_kRoot]
    norm_num
  · intro b _ hb
    rw [kZeroVec_apply_of_ne n k j hb]
    simp
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **The `j`-th zero lies on the equator.**  Its clutching coordinate is `0`, so no zero
of the `k`-fold section is a suspension point — which is the whole reason the constant
section had to move off `Fin.last n`. -/
theorem re_kZeroVec_last (n k : ℕ) (hn : 0 < n) (j : Fin (k + 1)) :
    (kZeroVec n k j (Fin.last n)).re = 0 := by
  rw [kZeroVec_apply_of_ne n k j (last_ne_zero n hn)]
  simp

/-- The `j`-th zero, as a point of `S^{2n+1}`. -/
def kZero (n k : ℕ) (j : Fin (k + 1)) : ↥(unitVectors (Fin (n + 1))) :=
  ⟨kZeroVec n k j, kZeroVec_mem n k j⟩

theorem kZero_injective (n k : ℕ) : Function.Injective (kZero n k) := by
  intro a b hab
  have h : kZeroVec n k a 0 = kZeroVec n k b 0 := by
    rw [show kZeroVec n k a = kZeroVec n k b from congrArg Subtype.val hab]
  exact kRoot_injective k (by rwa [kZeroVec_apply_zero, kZeroVec_apply_zero] at h)

/-! ## 4. The zero locus -/

/-- **The zero locus of the trivial block, at every rank.**  `Ψ_k x = −e₀` exactly at the
`k+1` points `ζ_j e₀` with `ζ_j^{k+1} = −1`.

This is the only geometric input the `k`-zero Step C needs from the map: everything else is
the one-zero argument transported around the rotation orbit.  Note that the proof splits on
`i = 0` versus `i ≠ 0` rather than enumerating the coordinates, which is what makes it
rank-generic; the rank-two file's `fin_cases` has no analogue here. -/
theorem psiVec_eq_neg_eZero_iff (n k : ℕ) (x : Fin (n + 1) → ℂ) :
    psiVec n k x = -eZero n ↔ ∃ j : Fin (k + 1), x = kZeroVec n k j := by
  constructor
  · intro h
    have h0 : joinC k (x 0) = -1 := by
      have hc := congrFun h 0
      rw [psiVec_apply_zero] at hc
      rw [hc, Pi.neg_apply, eZero_apply_zero]
    have hrest : ∀ i : Fin (n + 1), i ≠ 0 → x i = 0 := by
      intro i hi
      have hc := congrFun h i
      rw [psiVec_apply_of_ne n k x hi] at hc
      rw [hc, Pi.neg_apply, eZero_apply_of_ne n hi, neg_zero]
    obtain ⟨j, hj⟩ := exists_kRoot_of_pow_eq_neg_one ((joinC_eq_neg_one_iff k (x 0)).mp h0)
    refine ⟨j, funext fun i => ?_⟩
    rcases eq_or_ne i 0 with rfl | hi
    · rw [kZeroVec_apply_zero]
      exact hj
    · rw [kZeroVec_apply_of_ne n k j hi]
      exact hrest i hi
  · rintro ⟨j, rfl⟩
    funext i
    rcases eq_or_ne i 0 with rfl | hi
    · rw [psiVec_apply_zero, kZeroVec_apply_zero, Pi.neg_apply, eZero_apply_zero,
        joinC_eq_pow_of_norm_one (norm_kRoot k j) k, kRoot_pow]
    · rw [psiVec_apply_of_ne n k _ hi, kZeroVec_apply_of_ne n k j hi, Pi.neg_apply,
        eZero_apply_of_ne n hi, neg_zero]

/-! ## 5. The rotation, and the free orbit -/

/-- **The rotation of order `k+1`** in the `e₀`-plane, at exponent `m`.  It is the
restriction of a *linear* unitary of `ℂ^{n+1}`, so it is a homeomorphism of the sphere and
of the equator, and it is what makes every local contribution of the `k`-zero Step C
literally equal. -/
def kRot (n k m : ℕ) (x : Fin (n + 1) → ℂ) : Fin (n + 1) → ℂ :=
  Function.update x 0 (kUnity k ^ m * x 0)

@[simp] theorem kRot_apply_zero (n k m : ℕ) (x : Fin (n + 1) → ℂ) :
    kRot n k m x 0 = kUnity k ^ m * x 0 :=
  Function.update_self _ _ _

theorem kRot_apply_of_ne (n k m : ℕ) (x : Fin (n + 1) → ℂ) {i : Fin (n + 1)} (hi : i ≠ 0) :
    kRot n k m x i = x i :=
  Function.update_of_ne hi _ _

theorem norm_kRot_apply (n k m : ℕ) (x : Fin (n + 1) → ℂ) (i : Fin (n + 1)) :
    ‖kRot n k m x i‖ = ‖x i‖ := by
  rcases eq_or_ne i 0 with rfl | hi
  · rw [kRot_apply_zero, norm_mul, norm_pow, norm_kUnity, one_pow, one_mul]
  · rw [kRot_apply_of_ne n k m x hi]

theorem kRot_mem_unitVectors {n k m : ℕ} {x : Fin (n + 1) → ℂ}
    (hx : x ∈ unitVectors (Fin (n + 1))) : kRot n k m x ∈ unitVectors (Fin (n + 1)) := by
  rw [mem_unitVectors_iff, ← mem_unitVectors_iff.mp hx]
  exact Finset.sum_congr rfl fun i _ => by rw [norm_kRot_apply]

theorem continuous_kRot (n k m : ℕ) : Continuous (kRot n k m) := by
  refine continuous_pi fun i => ?_
  rcases eq_or_ne i 0 with rfl | hi
  · simp only [kRot_apply_zero]
    exact continuous_const.mul (continuous_apply 0)
  · simp only [kRot_apply_of_ne _ _ _ _ hi]
    exact continuous_apply i

/-- **`Ψ_k` is invariant under the rotation**, at every rank. -/
theorem psiVec_kRot (n k m : ℕ) (x : Fin (n + 1) → ℂ) :
    psiVec n k (kRot n k m x) = psiVec n k x := by
  funext i
  rcases eq_or_ne i 0 with rfl | hi
  · rw [psiVec_apply_zero, psiVec_apply_zero, kRot_apply_zero, joinC_kUnity_pow_mul]
  · rw [psiVec_apply_of_ne _ _ _ hi, psiVec_apply_of_ne _ _ _ hi,
      kRot_apply_of_ne _ _ _ _ hi]

/-- **The `k+1` zeros form one free orbit of the rotation**, based at the zeroth. -/
theorem kRot_kZeroVec_zero (n k : ℕ) (j : Fin (k + 1)) :
    kRot n k (j : ℕ) (kZeroVec n k 0) = kZeroVec n k j := by
  funext i
  rcases eq_or_ne i 0 with rfl | hi
  · rw [kRot_apply_zero, kZeroVec_apply_zero, kZeroVec_apply_zero]
    simp [kRoot]
  · rw [kRot_apply_of_ne _ _ _ _ hi, kZeroVec_apply_of_ne n k 0 hi,
      kZeroVec_apply_of_ne n k j hi]

end KGen

/-! ## 6. The rank-two bridges

Every rank-two name of `CharClass/LIXKMap.lean` that carries the rank is its own `KGen`
declaration at `n = 2`, **definitionally**.  All four cross only `Fin 3` versus `Fin (2+1)`
and the same `Pi.single` / `Function.update` at index `0`, so no `Decidable` instance is
written two ways and `rfl` sees the same term on both sides — which is exactly the
discriminator `sp-tower` recorded when their `jIncl` bridge was *not* `rfl`. -/

theorem eZero_two : KGen.eZero 2 = eOne := rfl

theorem negEZero_two : KGen.negEZero 2 = negEOne := rfl

theorem psiVec_two (k : ℕ) (x : Fin 3 → ℂ) : KGen.psiVec 2 k x = psiVec k x := rfl

theorem kZeroVec_two (k : ℕ) (j : Fin (k + 1)) : KGen.kZeroVec 2 k j = kZeroVec k j := rfl

theorem kZero_two (k : ℕ) (j : Fin (k + 1)) : KGen.kZero 2 k j = kZero k j := rfl

theorem kRot_two (k m : ℕ) (x : Fin 3 → ℂ) : KGen.kRot 2 k m x = kRot k m x := rfl

/-! Audited on every build. -/

#audit_axioms KGen.psiVec_eq_neg_eZero_iff
#audit_axioms KGen.kZero_injective
#audit_axioms KGen.psiVec_kRot
#audit_axioms KGen.re_kZeroVec_last

end GroupApproximation.CharClass
