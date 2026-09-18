import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVLowKZeroCore.Generation

/-!
# Independence modulo constant terms gives freeness over `L_k(1,2)`

Ingredient of `binaryLeavitt_idempotent_dichotomy` (manuscript
`simple_kazhdan_sofic_group.tex`, l.733-735, `sec:questions`, question Q2).

Let `w` be a finite family of columns whose entries lie in the `s`-word
filtration, and suppose the constant-term vectors `kappa ∘ w` are
`k`-linearly independent.  Then `w` is left `L`-linearly independent.

Proof.  Take a relation `∑ c_j • w_j = 0` with some `c_j ≠ 0`.  Let `d₀` be the
lowest degree occurring in the gradings of the `c_j`.  Write each entry as its
constant term plus a positive-degree part.  In degree `d₀` this gives
`∑_j constTerm (w_j δ) • x_j = 0`, where `x_j` is the degree-`d₀` coefficient of
`c_j`.  Applying any functional turns this into a `k`-linear dependence among
the `kappa (w j)`.  So every `x_j` vanishes, contradicting the choice of `d₀`.
-/

namespace GroupApproximation.Full.LVLowKZeroCore

open GroupApproximation.BinaryLeavitt

noncomputable section

variable (k : Type) [Field k]

/-- If `c` vanishes below degree `d₀` and `x ∈ fil k n`, then the
degree-`d₀` coefficient of `c * x` is `constTerm x` times that of `c`. -/
theorem coeff_grade_mul_eq (c x : BinaryLeavittAlgebra k) {n : ℕ} (hx : x ∈ fil k n)
    (d₀ : ℤ) (hc : ∀ d : ℤ, d < d₀ → (grade k c).coeff d = 0) :
    (grade k (c * x)).coeff d₀ = constTerm k x • (grade k c).coeff d₀ := by
  have hp := sub_constTerm_mem_pos k hx
  have hcx : c * x = c * (x - constTerm k x • (1 : BinaryLeavittAlgebra k)) +
      constTerm k x • c := by
    rw [mul_sub, mul_smul_comm, mul_one, sub_add_cancel]
  rw [hcx, map_add, map_mul, map_smul, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
    coeff_mul_eq_zero_of_lt _ _ d₀ hc (coeff_grade_eq_zero_of_mem_pos k hp), zero_add,
    AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply]

/-- **Freeness.**  A family of filtered columns that is independent modulo
constant terms is left `L`-linearly independent. -/
theorem eq_zero_of_sum_smul_eq_zero {m n r : ℕ}
    (w : Fin r → ((Fin m → Fin 2) → BinaryLeavittAlgebra k))
    (hw : ∀ j δ, w j δ ∈ fil k n) (hli : LinearIndependent k (kappa k m ∘ w))
    (c : Fin r → BinaryLeavittAlgebra k) (hc : ∑ j, c j • w j = 0) : c = 0 := by
  by_contra hne
  obtain ⟨j₀, hj₀⟩ : ∃ j, c j ≠ 0 := by
    by_contra h
    exact hne (funext fun j => Classical.byContradiction fun hj => h ⟨j, hj⟩)
  -- The lowest degree occurring in the gradings of the `c j`.
  obtain ⟨d₀, ⟨j₁, hj₁⟩, hmin⟩ : ∃ d₀ : ℤ, (∃ j, (grade k (c j)).coeff d₀ ≠ 0) ∧
      ∀ j d, (grade k (c j)).coeff d ≠ 0 → d₀ ≤ d := by
    have hS : (Finset.univ.biUnion fun j => (grade k (c j)).coeff.support).Nonempty := by
      obtain ⟨d, hd⟩ := Finsupp.support_nonempty_iff.mpr
        (fun h => grade_ne_zero k hj₀ (AddMonoidAlgebra.coeff_eq_zero.mp h))
      exact ⟨d, Finset.mem_biUnion.mpr ⟨j₀, Finset.mem_univ _, hd⟩⟩
    obtain ⟨j₁, -, hj₁⟩ := Finset.mem_biUnion.mp (Finset.min'_mem _ hS)
    refine ⟨_, ⟨j₁, Finsupp.mem_support_iff.mp hj₁⟩, fun j d hd => Finset.min'_le _ _ ?_⟩
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, Finsupp.mem_support_iff.mpr hd⟩
  have hlow : ∀ j d, d < d₀ → (grade k (c j)).coeff d = 0 := fun j d hd =>
    Classical.byContradiction fun h => absurd (hmin j d h) (not_le.mpr hd)
  -- Degree `d₀` of every row of the relation.
  have hrow : ∀ δ, ∑ j, constTerm k (w j δ) • (grade k (c j)).coeff d₀ = 0 := by
    intro δ
    have h : ∑ j, c j * w j δ = 0 := by
      have h' := congrFun hc δ
      rw [Finset.sum_apply] at h'
      exact h'
    calc ∑ j, constTerm k (w j δ) • (grade k (c j)).coeff d₀
        = ∑ j, (grade k (c j * w j δ)).coeff d₀ :=
          Finset.sum_congr rfl fun j _ =>
            (coeff_grade_mul_eq k (c j) (w j δ) (hw j δ) d₀ (hlow j)).symm
      _ = (grade k (∑ j, c j * w j δ)).coeff d₀ := by
          rw [map_sum, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
      _ = 0 := by
          rw [h, map_zero, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  -- Every degree-`d₀` coefficient vanishes.
  have hx : ∀ j, (grade k (c j)).coeff d₀ = 0 := by
    intro j
    refine (Module.forall_dual_apply_eq_zero_iff k _).mp fun ψ => ?_
    have hdep : ∑ i, ψ ((grade k (c i)).coeff d₀) • (kappa k m ∘ w) i = 0 := by
      funext δ
      rw [Finset.sum_apply, Pi.zero_apply, ← map_zero ψ, ← hrow δ, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, Pi.smul_apply, Function.comp_apply, kappa_apply, smul_eq_mul, smul_eq_mul,
        mul_comm]
    exact (Fintype.linearIndependent_iff.mp hli) _ hdep j
  exact hj₁ (hx j₁)

end

end GroupApproximation.Full.LVLowKZeroCore
