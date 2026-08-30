import GroupApproximation.Sofic.NormMFResidualDetector

/-!
# Group-level consequences of the operator-norm MF residual

Consequences built on the residual machinery of `NormMFResidualDetector`:

* `IsNormApproximable.comap` / `IsWeakMF.comap` / `IsWeakMF.subgroup` —
  weak-MF approximability pulls back along injective homomorphisms; in
  particular every subgroup of a weak-MF group is weak-MF
  for every subgroup of a weak-MF group.
* `not_injective_of_normMFInvisible` — a group with a nontrivial
  MF-invisible element admits no injective homomorphism into any
  operator-norm matrix ultraproduct.
* `not_isWeakMF_of_map_ne_one` — radical portability: any group in which
  an MF-invisible element survives under a homomorphism is itself not
  weak-MF.
* `uniform_invisibility` — invisibility
  upgrades to a uniform statement by compactness.  For every tolerance
  `ε` there are a defect budget `δ` and a finite set `F₀` such that every
  unitary matrix family that is `δ`-multiplicative on `F₀` moves the
  invisible element within `ε` of the identity.  The proof diagonalizes
  a hypothetical sequence of counterexamples into a single homomorphism
  to an operator-norm matrix ultraproduct and applies invisibility.

-/

namespace GroupApproximation

open Filter Matrix
open scoped Matrix.Norms.L2Operator

universe u v

variable {G : Type u} [Group G]

/-! ## Pulling approximability back along injective homomorphisms -/

/-! ## No faithful ultraproduct representations -/

/-! ## Uniform invisibility -/

/-- **Uniform invisibility.** If `x`
is killed by every homomorphism to every operator-norm matrix
ultraproduct, then for every `ε > 0` there are a defect budget `δ > 0`
and a finite subset `F₀` such that every family of finite unitary
matrices with multiplicative defect at most `δ` on `F₀` moves `x` to
within `ε` of the identity.  The proof is the compactness diagonal: a
sequence of counterexamples at budgets `1/(k+1)` over an exhausting
sequence of finite sets assembles into a homomorphism to an operator-norm
matrix ultraproduct in which `x` survives at norm `ε`, contradicting
invisibility. -/
theorem uniform_invisibility [Countable G] {x : G}
    (hx : NormMFInvisible x) :
    ∀ ε : ℝ, 0 < ε → ∃ (δ : ℝ) (F₀ : Finset G), 0 < δ ∧
      ∀ (Y : FiniteModel) (φ : G → Matrix.unitaryGroup Y ℂ),
        (∀ g ∈ F₀, ∀ h ∈ F₀,
          ‖(φ (g * h) : Matrix Y Y ℂ) -
            (φ g : Matrix Y Y ℂ) * φ h‖ ≤ δ) →
        ‖(φ x : Matrix Y Y ℂ) - 1‖ < ε := by
  classical
  intro ε hε
  by_contra hcon
  push Not at hcon
  obtain ⟨e, he⟩ := exists_surjective_nat G
  have hstep : ∀ k : ℕ, ∃ (Y : FiniteModel)
      (φ : G → Matrix.unitaryGroup Y ℂ),
      (∀ g ∈ (Finset.range (k + 1)).image e,
        ∀ h ∈ (Finset.range (k + 1)).image e,
        ‖(φ (g * h) : Matrix Y Y ℂ) -
          (φ g : Matrix Y Y ℂ) * φ h‖ ≤ 1 / ((k : ℝ) + 1)) ∧
      ε ≤ ‖(φ x : Matrix Y Y ℂ) - 1‖ := by
    intro k
    exact hcon (1 / ((k : ℝ) + 1)) ((Finset.range (k + 1)).image e)
      (by positivity)
  choose Y φ hdef hfar using hstep
  set 𝒰 : Ultrafilter ℕ := Ultrafilter.of Filter.cofinite
  have hcof : (𝒰 : Filter ℕ) ≤ Filter.cofinite := Ultrafilter.of_le _
  -- the diagonal family is asymptotically multiplicative
  have hnull : ∀ g h : G,
      (fun k => φ k g * φ k h)⁻¹ * (fun k => φ k (g * h)) ∈
        nullOpSubgroup 𝒰 Y := by
    intro g h ε' hε'
    obtain ⟨i, hi⟩ := he g
    obtain ⟨j, hj⟩ := he h
    obtain ⟨K, hK⟩ := exists_nat_gt (1 / ε')
    refine eventually_of_atTop hcof (max (max i j) K) (fun k hk => ?_)
    have hik : i ≤ k :=
      le_trans (le_trans (le_max_left i j) (le_max_left _ K)) hk
    have hjk : j ≤ k :=
      le_trans (le_trans (le_max_right i j) (le_max_left _ K)) hk
    have hKk : K ≤ k := le_trans (le_max_right _ K) hk
    have hg : g ∈ (Finset.range (k + 1)).image e :=
      Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (by lia), hi⟩
    have hh : h ∈ (Finset.range (k + 1)).image e :=
      Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr (by lia), hj⟩
    change opLength (Y k) ((φ k g * φ k h)⁻¹ * φ k (g * h)) < ε'
    rw [opLength_inv_mul]
    refine (hdef k g hg h hh).trans_lt ?_
    have hKpos : (0 : ℝ) < (K : ℝ) + 1 := by positivity
    have hkpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hcast : ((K : ℝ) + 1) ≤ ((k : ℝ) + 1) := by
      exact_mod_cast Nat.add_le_add_right hKk 1
    have hεK : 1 / ((K : ℝ) + 1) < ε' := by
      rw [div_lt_iff₀ hKpos]
      have hK' : 1 / ε' < (K : ℝ) := hK
      rw [div_lt_iff₀ hε'] at hK'
      nlinarith only [hK', hε']
    calc 1 / ((k : ℝ) + 1) ≤ 1 / ((K : ℝ) + 1) :=
          one_div_le_one_div_of_le hKpos hcast
      _ < ε' := hεK
  -- assemble the homomorphism to the ultraproduct
  set rho : G →* UniversalWeakMF 𝒰 Y :=
    MonoidHom.mk' (fun g => QuotientGroup.mk (fun k => φ k g))
      (fun g h => by
        rw [← QuotientGroup.mk_mul]
        exact (QuotientGroup.eq.mpr (hnull g h)).symm)
  -- invisibility kills `x` in the ultraproduct
  have hone : rho x = 1 := hx ℕ 𝒰 Y rho
  have hmem : (fun k => φ k x) ∈ nullOpSubgroup 𝒰 Y := by
    rw [show rho x = QuotientGroup.mk (fun k => φ k x) from rfl] at hone
    exact (QuotientGroup.eq_one_iff _).mp hone
  -- but the counterexamples keep `x` at distance `ε`
  obtain ⟨k, hk⟩ := (hmem ε hε).exists
  rw [show opLength (Y k) (φ k x) =
      ‖(φ k x : Matrix (Y k) (Y k) ℂ) - 1‖ from rfl] at hk
  exact absurd hk (not_lt_of_ge (hfar k))

end GroupApproximation
