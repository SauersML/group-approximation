import GroupApproximation.Sofic.Sofic

/-!
# Asymptotically multiplicative permutation models

Kazhdan averaging only uses approximate multiplication; metric faithfulness
is irrelevant to that argument.  This structure records the exact smaller
interface.  Keeping it separate from `SoficApproximation` is important when
one passes to individual expander components: their completed labels remain
asymptotically multiplicative after discarding bad component mass, but need
not be faithful on any one component.
-/

namespace GroupApproximation

/-- A diverging sequence of finite permutation models whose multiplication
defect tends to zero.  No separation or faithfulness condition is imposed. -/
structure MultiplicativeApproximation (G : Type*) [Group G] where
  model : ℕ → FiniteModel
  map : (n : ℕ) → G → Equiv.Perm (model n)
  card_tendsToInfinity : ∀ M : ℕ, ∃ N : ℕ, ∀ n ≥ N,
    M ≤ Fintype.card (model n)
  asymptoticallyMultiplicative :
    ∀ (g h : G) (ε : ℝ), 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
      hammingDistance (model n) (map n (g * h)) (map n g * map n h) < ε

variable {K J : Type*} [Group K] [Group J]

/-- The finite set of permutations assigned to a fixed set of generators of
the first factor.  Only the assigned maps are used; metric faithfulness is
irrelevant. -/
noncomputable def multiplicativeProductLabels
    (A : MultiplicativeApproximation (K × J)) (n : ℕ)
    (T : Finset K) : Finset (Equiv.Perm (A.model n)) := by
  classical
  exact T.image fun k ↦ A.map n (k, 1)

namespace MultiplicativeApproximation

variable {G : Type*} [Group G]

/-- Forget metric faithfulness from a sofic approximation.  This is reducible
so consumers see exactly the same finite model and label map, including in
types depending on the model's carrier. -/
abbrev ofSofic (S : SoficApproximation G) : MultiplicativeApproximation G where
  model := S.model
  map := S.map
  card_tendsToInfinity := S.card_tendsToInfinity
  asymptoticallyMultiplicative := S.asymptoticallyMultiplicative

instance : Coe (SoficApproximation G) (MultiplicativeApproximation G) :=
  ⟨ofSofic⟩

@[simp] theorem ofSofic_model (S : SoficApproximation G) (n : ℕ) :
    (ofSofic S).model n = S.model n := rfl

@[simp] theorem ofSofic_map (S : SoficApproximation G) (n : ℕ) :
    (ofSofic S).map n = S.map n := rfl

/-- Approximate multiplication alone forces the assigned identity to tend to
the genuine identity permutation. -/
theorem map_one_close (A : MultiplicativeApproximation G)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N,
      hammingDistance (A.model n) (A.map n 1) 1 < ε := by
  obtain ⟨N, hN⟩ := A.asymptoticallyMultiplicative 1 1 ε hε
  refine ⟨N, fun n hn ↦ ?_⟩
  have h := hN n hn
  simp only [one_mul] at h
  calc
    hammingDistance (A.model n) (A.map n 1) 1 =
        hammingDistance (A.model n) 1 (A.map n 1) :=
      hammingDistance_comm _ _ _
    _ = hammingDistance (A.model n) ((A.map n 1)⁻¹ * A.map n 1)
        ((A.map n 1)⁻¹ * (A.map n 1 * A.map n 1)) := by simp
    _ = hammingDistance (A.model n) (A.map n 1)
        (A.map n 1 * A.map n 1) :=
      hammingDistance_left_invariant _ _ _ _
    _ < ε := h

/-- Approximate multiplication also identifies the assigned `g⁻¹h` with
the relative permutation `(map g)⁻¹ * map h`. -/
theorem inv_mul_close_eventually (A : MultiplicativeApproximation G)
    (g h : G) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N,
      hammingDistance (A.model n) (A.map n (g⁻¹ * h))
        ((A.map n g)⁻¹ * A.map n h) < ε := by
  have hthird : 0 < ε / 3 := by positivity
  obtain ⟨Nmul, hNmul⟩ :=
    A.asymptoticallyMultiplicative g⁻¹ h (ε / 3) hthird
  obtain ⟨Ninv, hNinv⟩ :=
    A.asymptoticallyMultiplicative g⁻¹ g (ε / 3) hthird
  obtain ⟨None, hNone⟩ := A.map_one_close (ε / 3) hthird
  refine ⟨max Nmul (max Ninv None), fun n hn ↦ ?_⟩
  have hnmul : Nmul ≤ n := by omega
  have hninv : Ninv ≤ n := by omega
  have hnone : None ≤ n := by omega
  have hmul := hNmul n hnmul
  have hinvMul := hNinv n hninv
  have hone := hNone n hnone
  simp only [inv_mul_cancel] at hinvMul
  have hinv : hammingDistance (A.model n) (A.map n g⁻¹)
      (A.map n g)⁻¹ < 2 * (ε / 3) := by
    have htri := hammingDistance_triangle (A.model n)
      (A.map n g⁻¹ * A.map n g) (A.map n 1) 1
    have hprod : hammingDistance (A.model n)
        (A.map n g⁻¹ * A.map n g) 1 < 2 * (ε / 3) := by
      rw [hammingDistance_comm] at hinvMul
      linarith
    calc
      hammingDistance (A.model n) (A.map n g⁻¹) (A.map n g)⁻¹ =
          hammingDistance (A.model n)
            (A.map n g⁻¹ * A.map n g) ((A.map n g)⁻¹ * A.map n g) := by
        rw [hammingDistance_right_invariant]
      _ = hammingDistance (A.model n) (A.map n g⁻¹ * A.map n g) 1 := by simp
      _ < 2 * (ε / 3) := hprod
  have hright : hammingDistance (A.model n)
      (A.map n g⁻¹ * A.map n h) ((A.map n g)⁻¹ * A.map n h) <
        2 * (ε / 3) := by
    rw [hammingDistance_right_invariant]
    exact hinv
  have htri := hammingDistance_triangle (A.model n)
    (A.map n (g⁻¹ * h)) (A.map n g⁻¹ * A.map n h)
    ((A.map n g)⁻¹ * A.map n h)
  linarith

/-- Reindex along a pointwise cofinal map. -/
def reindex (A : MultiplicativeApproximation G) (φ : ℕ → ℕ)
    (hφ : ∀ n, n ≤ φ n) : MultiplicativeApproximation G where
  model n := A.model (φ n)
  map n := A.map (φ n)
  card_tendsToInfinity M := by
    obtain ⟨N, hN⟩ := A.card_tendsToInfinity M
    exact ⟨N, fun n hn ↦ hN (φ n) (hn.trans (hφ n))⟩
  asymptoticallyMultiplicative g h ε hε := by
    obtain ⟨N, hN⟩ := A.asymptoticallyMultiplicative g h ε hε
    exact ⟨N, fun n hn ↦ hN (φ n) (hn.trans (hφ n))⟩

@[simp] theorem reindex_model (A : MultiplicativeApproximation G)
    (φ : ℕ → ℕ) (hφ : ∀ n, n ≤ φ n) (n : ℕ) :
    (A.reindex φ hφ).model n = A.model (φ n) := rfl

@[simp] theorem reindex_map (A : MultiplicativeApproximation G)
    (φ : ℕ → ℕ) (hφ : ∀ n, n ≤ φ n) (n : ℕ) :
    (A.reindex φ hφ).map n = A.map (φ n) := rfl

end MultiplicativeApproximation
end GroupApproximation
