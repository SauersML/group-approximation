import GroupApproximation.Analysis.CStarKOne

/-!
# A single unitary refutes `K_1`-injectivity

`K1Injective A` says the canonical map `U(A)/U_0(A) → K_1(A)` is injective.  Refuting it
looks as though it requires knowing `K_1(A)`.  It does not.  The whole of `K_1(A)` enters
only through the identity

    kappa [u] = iota_2 [diag (u, 1)],

so a unitary `u` with

    u ∉ U_0(A)      and      diag (u, 1) ∈ U_0(M_2(A))

already gives `kappa [u] = 1` with `[u] ≠ 1`.

This is the load-bearing reduction for STW Problem LIX.  The witness constructed in
`research/artifacts/stw59-simple-ah-k1-counterexample-manuscript-2026-09-05.md` satisfies
exactly these two conditions: the manuscript's Theorem 1 proof ends by observing that
`diag(u, 1)` contracts already in `U(3)` over the base, so its image `diag(v, 1_A)` is
null-homotopic in `U(M_2(A))`, while `v ∉ U_0(A)` is the parity obstruction.

No Bott periodicity, no Morita invariance and no continuity of `K`-theory is used, and
none of those exist in Mathlib.
-/

namespace GroupApproximation

universe u

noncomputable section

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- `diag (u, 1) ∈ U(M_2(A))`: the image of a unitary `u ∈ U(A)` under the 1×1 matrix
identification followed by the block inclusion `M_1(A) → M_2(A)`. -/
def diagOne (u : unitary A) : unitary (CStarMat 2 A) :=
  blockOneUnitary (by norm_num : (1 : ℕ) ≤ 2) (unitaryOneByOne A u)

omit [PartialOrder A] [StarOrderedRing A] in
theorem coe_diagOne (u : unitary A) :
    ((diagOne u : unitary (CStarMat 2 A)) : CStarMat 2 A)
      = blockOne (toOneByOneHom A (u : A)) 2 := rfl

theorem coe_diagOne_apply (u : unitary A) (i j : Fin 2) :
    ((diagOne u : unitary (CStarMat 2 A)) : CStarMat 2 A) i j =
      if (i : ℕ) = 0 then (if (j : ℕ) = 0 then (u : A) else 0)
      else (if (j : ℕ) = 0 then 0 else 1) := by
  have hi2 : (i : ℕ) < 2 := i.isLt
  have hj2 : (j : ℕ) < 2 := j.isLt
  rw [coe_diagOne]
  by_cases hi : (i : ℕ) = 0
  · have hi' : (i : ℕ) < 1 := by omega
    by_cases hj : (j : ℕ) = 0
    · have hj' : (j : ℕ) < 1 := by omega
      rw [blockOne_apply_of_lt_of_lt _ i j hi' hj', toOneByOneHom_apply, if_pos hi, if_pos hj]
    · have hj' : ¬ ((j : ℕ) < 1) := by omega
      rw [blockOne_apply_of_lt_of_not_lt _ i j hi' hj', if_pos hi, if_neg hj]
  · have hi' : ¬ ((i : ℕ) < 1) := by omega
    by_cases hj : (j : ℕ) = 0
    · have hj' : (j : ℕ) < 1 := by omega
      rw [blockOne_apply_of_not_lt_of_lt _ i j hi' hj', if_neg hi, if_pos hj]
    · have hj' : ¬ ((j : ℕ) < 1) := by omega
      rw [blockOne_apply_of_not_lt_of_not_lt _ i j hi' hj', if_neg hi, if_neg hj,
        if_pos (show i = j from Fin.eq_of_val_eq (by omega))]

/-- The image of `[u]` under `kappa` is the class of `diag (u, 1)` at level two of the tower.
This single identity is the whole of `K_1(A)` that the reduction below needs. -/
theorem kappa_mk_eq_kOneIota_two (u : unitary A) :
    kappa A (QuotientGroup.mk u) = kOneIota A 2 (QuotientGroup.mk (diagOne u)) :=
  (kOneIota_kOneMap A (by norm_num : (1 : ℕ) ≤ 2)
    (QuotientGroup.mk (unitaryOneByOne A u))).symm

/-- If `diag (u, 1)` is null-homotopic in `U(M_2(A))`, then `u` has trivial class in `K_1(A)`. -/
theorem kappa_mk_eq_one_of_diagOne_mem {u : unitary A}
    (hdiag : diagOne u ∈ unitaryComponentOne (CStarMat 2 A)) :
    kappa A (QuotientGroup.mk u) = 1 := by
  rw [kappa_mk_eq_kOneIota_two u,
    show (QuotientGroup.mk (diagOne u) : KOneLevel A 2) = 1 from
      unitaryClass_eq_one_iff.mpr hdiag,
    map_one]

/-- **The reduction.**  A unitary `u` of `A` which is not null-homotopic in `U(A)` but whose
block sum `diag (u, 1)` is null-homotopic in `U(M_2(A))` refutes `K_1`-injectivity of `A`. -/
theorem not_k1Injective_of_diagOne_mem {u : unitary A}
    (hu : u ∉ unitaryComponentOne A)
    (hdiag : diagOne u ∈ unitaryComponentOne (CStarMat 2 A)) :
    ¬ K1Injective A := by
  intro hinj
  refine hu ?_
  rw [← unitaryClass_eq_one_iff]
  refine hinj ?_
  rw [map_one]
  exact kappa_mk_eq_one_of_diagOne_mem hdiag

/-- The same reduction with both hypotheses phrased by paths: `u` is not joined to `1` in
`U(A)`, but `diag (u, 1)` is joined to `1` in `U(M_2(A))`. -/
theorem not_k1Injective_of_joined_diagOne {u : unitary A}
    (hu : ¬ Joined (1 : unitary A) u)
    (hdiag : Joined (1 : unitary (CStarMat 2 A)) (diagOne u)) :
    ¬ K1Injective A :=
  not_k1Injective_of_diagOne_mem hu hdiag

/-- The existence form of the reduction: a single unitary with these two properties refutes
`K_1`-injectivity. -/
theorem not_k1Injective_of_exists_witness
    (h : ∃ u : unitary A, u ∉ unitaryComponentOne A ∧
      diagOne u ∈ unitaryComponentOne (CStarMat 2 A)) :
    ¬ K1Injective A := by
  obtain ⟨u, hu, hdiag⟩ := h
  exact not_k1Injective_of_diagOne_mem hu hdiag

end

end GroupApproximation
