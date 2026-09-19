import GroupApproximation.PropertyT.IntegralColumnPlaneReduction

/-!
# Root estimates supplied directly by the integral control set

The integral control set contains the unit coefficient and every free
generator coefficient in every elementary root.  The elementary commutator
recursion therefore controls every word-monomial coefficient.  Its constant
grows exponentially with word length, so this estimate does not prove the
uniform `RootCoefficientDisplacementBound` isolated in
`IntegralColumnPlaneReduction`.

This file records that exact boundary.  It also uses the permutation symmetry
of the three matrix coordinates to reduce the remaining coefficient estimate
to one fixed root.  That reduction loses no constant: the integral control set
contains the same coefficient in every ordered root and is therefore invariant
under reindexing.
-/

namespace GroupApproximation

universe u v

namespace IntegralColumnPlaneRootReduction

open IntegralCharacterMass IntegralColumnPlaneReduction

/-! ### Quantitative transport between adjacent roots -/

/-- Changing the terminal index of a root is one Steinberg commutator.  This
is the basic quantitative recurrence in the rank-three relative-`(T)`
calculus. -/
theorem norm_elementaryRoot_change_target_displacement_le
    {R : Type u} [Ring R]
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (rho : elementaryGroup (Fin 3) R →* (E ≃ₗᵢ[ℝ] E)) (z : E)
    (i j k : Fin 3) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (a : R) :
    ‖rho (elementaryRoot i k hik a) z - z‖ ≤
      2 * ‖rho (elementaryRoot i j hij a) z - z‖ +
        2 * ‖rho (elementaryRoot j k hjk 1) z - z‖ := by
  have h := norm_commutator_displacement_le rho z
    (elementaryRoot i j hij a) (elementaryRoot j k hjk 1)
  rwa [elementaryRoot_commutator, mul_one] at h

/-- Changing the initial index is likewise one Steinberg commutator. -/
theorem norm_elementaryRoot_change_source_displacement_le
    {R : Type u} [Ring R]
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (rho : elementaryGroup (Fin 3) R →* (E ≃ₗᵢ[ℝ] E)) (z : E)
    (k i j : Fin 3) (hki : k ≠ i) (hij : i ≠ j) (hkj : k ≠ j)
    (a : R) :
    ‖rho (elementaryRoot k j hkj a) z - z‖ ≤
      2 * ‖rho (elementaryRoot k i hki 1) z - z‖ +
        2 * ‖rho (elementaryRoot i j hij a) z - z‖ := by
  have h := norm_commutator_displacement_le rho z
    (elementaryRoot k i hki 1) (elementaryRoot i j hij a)
  rwa [elementaryRoot_commutator, one_mul] at h

/-! ### Reindexing the integral control set -/

/-- Reindex an ordered `A₂` root by a permutation of the three matrix
coordinates. -/
def reindexA2Root (e : Equiv.Perm (Fin 3)) (a : A2Root) : A2Root :=
  ⟨(e a.1.1, e a.1.2), e.injective.ne a.2⟩

/-- Reindexing an integral control element only reindexes its ordered root;
its coefficient is unchanged. -/
@[simp] theorem elementaryReindexEquiv_integralControlElement
    (X : Type u) [Fintype X] (e : Equiv.Perm (Fin 3))
    (p : A2Root × Option X) :
    elementaryReindexEquiv (R := FreeAlgebra ℤ X) e
        (integralControlElement X p) =
      integralControlElement X (reindexA2Root e p.1, p.2) := by
  exact elementaryReindexEquiv_elementaryRoot
    e p.1.1.1 p.1.1.2 p.1.2 (integralControlCoefficient X p.2)

/-- The integral control set is invariant under every permutation of the
three matrix coordinates. -/
theorem elementaryReindexEquiv_mem_integralControlSet
    (X : Type u) [Fintype X] (e : Equiv.Perm (Fin 3))
    {g : elementaryGroup (Fin 3) (FreeAlgebra ℤ X)}
    (hg : g ∈ integralControlSet X) :
    elementaryReindexEquiv (R := FreeAlgebra ℤ X) e g ∈
      integralControlSet X := by
  classical
  rw [integralControlSet, Finset.mem_image] at hg ⊢
  obtain ⟨p, _, rfl⟩ := hg
  exact ⟨(reindexA2Root e p.1, p.2), Finset.mem_univ _, by simp⟩

/-- The coordinate map which sends `0` to `i`, `1` to `k`, and `2` to the
remaining coordinate. -/
def orderedPairReindex (i k : Fin 3) : Fin 3 → Fin 3 :=
  ![i, k, a2ThirdIndex i k]

theorem orderedPairReindex_injective (i k : Fin 3) (hik : i ≠ k) :
    Function.Injective (orderedPairReindex i k) := by
  intro s t hst
  fin_cases i <;> fin_cases k <;> fin_cases s <;> fin_cases t <;>
    simp_all [orderedPairReindex, a2ThirdIndex]

/-- The coordinate permutation determined by an ordered pair of distinct
indices. -/
noncomputable def orderedPairReindexEquiv (i k : Fin 3) (hik : i ≠ k) :
    Equiv.Perm (Fin 3) :=
  Equiv.ofBijective (orderedPairReindex i k)
    ⟨orderedPairReindex_injective i k hik,
      Finite.surjective_of_injective (orderedPairReindex_injective i k hik)⟩

@[simp] theorem orderedPairReindexEquiv_zero
    (i k : Fin 3) (hik : i ≠ k) :
    orderedPairReindexEquiv i k hik 0 = i := rfl

@[simp] theorem orderedPairReindexEquiv_one
    (i k : Fin 3) (hik : i ≠ k) :
    orderedPairReindexEquiv i k hik 1 = k := rfl

/-! ### Reduction to one fixed root -/

/-- The remaining integral coefficient estimate restricted to the fixed root
`(0,1)`.  The representation is still arbitrary, so coordinate reindexing can
transport this estimate to every ordered root. -/
def IntegralFixedRootCoefficientDisplacementBound
    (X : Type u) [Fintype X] (C : ℝ) : Prop :=
  ∀ (E : Type v) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E],
    ∀ (rho : elementaryGroup (Fin 3) (FreeAlgebra ℤ X) →* (E ≃ₗᵢ[ℝ] E))
      (z : E) (delta : ℝ),
      0 < delta →
        (∀ s ∈ integralControlSet X, ‖rho s z - z‖ < delta) →
          ∀ a : FreeAlgebra ℤ X,
            ‖rho (elementaryRoot (0 : Fin 3) (1 : Fin 3) (by decide) a) z - z‖ ≤
              C * delta

/-- Control of the fixed root `(0,1)` controls every root with exactly the
same constant.  Apply the fixed-root hypothesis to the representation
precomposed with the coordinate permutation sending `(0,1)` to `(i,k)`; the
preceding invariance theorem supplies near invariance for that representation.
-/
theorem rootCoefficientDisplacementBound_of_fixedRootBound
    (X : Type u) [Fintype X] {C : ℝ}
    (hfixed : IntegralFixedRootCoefficientDisplacementBound.{u, v} X C) :
    RootCoefficientDisplacementBound.{u, v}
      (FreeAlgebra ℤ X) (integralControlSet X) C := by
  intro E _ _ _ rho z delta hdelta hnear i k hik a
  let e : Equiv.Perm (Fin 3) := orderedPairReindexEquiv i k hik
  let rho' : elementaryGroup (Fin 3) (FreeAlgebra ℤ X) →* (E ≃ₗᵢ[ℝ] E) :=
    rho.comp (elementaryReindexEquiv (R := FreeAlgebra ℤ X) e).toMonoidHom
  have hnear' : ∀ s ∈ integralControlSet X, ‖rho' s z - z‖ < delta := by
    intro s hs
    exact hnear _ (elementaryReindexEquiv_mem_integralControlSet X e hs)
  have hbound := hfixed E rho' z delta hdelta hnear' a
  simpa [rho', e] using hbound

/-- The all-root estimate restricts to the fixed root without any change in
the constant. -/
theorem fixedRootBound_of_rootCoefficientDisplacementBound
    (X : Type u) [Fintype X] {C : ℝ}
    (hroot : RootCoefficientDisplacementBound.{u, v}
      (FreeAlgebra ℤ X) (integralControlSet X) C) :
    IntegralFixedRootCoefficientDisplacementBound.{u, v} X C := by
  intro E _ _ _ rho z delta hdelta hnear a
  exact hroot E rho z delta hdelta hnear
    (0 : Fin 3) (1 : Fin 3) (by decide) a

/-- The missing all-root estimate is equivalent, with no loss in its
constant, to the estimate on the single fixed root `(0,1)`. -/
theorem rootCoefficientDisplacementBound_iff_fixedRootBound
    (X : Type u) [Fintype X] (C : ℝ) :
    RootCoefficientDisplacementBound.{u, v}
        (FreeAlgebra ℤ X) (integralControlSet X) C ↔
      IntegralFixedRootCoefficientDisplacementBound.{u, v} X C :=
  ⟨fixedRootBound_of_rootCoefficientDisplacementBound X,
    rootCoefficientDisplacementBound_of_fixedRootBound X⟩

/-- Consequently, the integral column-plane mass estimate exists exactly when
the single fixed root admits a uniform coefficient-displacement estimate. -/
theorem exists_columnPlaneMassBound_iff_exists_fixedRootBound
    (X : Type u) [Fintype X] :
    (∃ C : ℝ, ColumnPlaneMassBound.{u, v} (FreeAlgebra ℤ X)
        (integralControlSet X) C) ↔
      ∃ C : ℝ, IntegralFixedRootCoefficientDisplacementBound.{u, v} X C := by
  rw [integral_exists_columnPlaneMassBound_iff_exists_rootCoefficientBound X]
  constructor
  · rintro ⟨C, hC⟩
    exact ⟨C, fixedRootBound_of_rootCoefficientDisplacementBound X hC⟩
  · rintro ⟨C, hC⟩
    exact ⟨C, rootCoefficientDisplacementBound_of_fixedRootBound X hC⟩

/-- Near invariance under the integral control set includes near invariance
under the unit coefficient in every elementary root. -/
theorem norm_integral_unitRoot_displacement_lt_of_controlSet_near
    (X : Type u) [Fintype X]
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (rho : elementaryGroup (Fin 3) (FreeAlgebra ℤ X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) (delta : ℝ)
    (hnear : ∀ s ∈ integralControlSet X, ‖rho s z - z‖ < delta)
    (i j : Fin 3) (hij : i ≠ j) :
    ‖rho (elementaryRoot i j hij 1) z - z‖ < delta := by
  let a : A2Root := ⟨(i, j), hij⟩
  let p : A2Root × Option X := (a, none)
  have hp := hnear (integralControlElement X p)
    (integralControlElement_mem X p)
  simpa [p, a, integralControlElement, integralControlCoefficient] using hp

/-- If one root coefficient is bounded by `C * delta` and the unit roots are
`delta`-small, one change of terminal index replaces `C` by `2 * C + 2`.
Iterating the elementary commutator route therefore gives the explicit
constants `4 * C + 6` after two changes and `8 * C + 14` after three. -/
theorem norm_integral_change_target_displacement_le
    (X : Type u) [Fintype X]
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (rho : elementaryGroup (Fin 3) (FreeAlgebra ℤ X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) (delta C : ℝ)
    (hnear : ∀ s ∈ integralControlSet X, ‖rho s z - z‖ < delta)
    (i j k : Fin 3) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (a : FreeAlgebra ℤ X)
    (ha : ‖rho (elementaryRoot i j hij a) z - z‖ ≤ C * delta) :
    ‖rho (elementaryRoot i k hik a) z - z‖ ≤
      (2 * C + 2) * delta := by
  calc
    ‖rho (elementaryRoot i k hik a) z - z‖ ≤
        2 * ‖rho (elementaryRoot i j hij a) z - z‖ +
          2 * ‖rho (elementaryRoot j k hjk 1) z - z‖ :=
      norm_elementaryRoot_change_target_displacement_le
        rho z i j k hij hjk hik a
    _ ≤ 2 * (C * delta) + 2 * delta := by
      gcongr
      exact (norm_integral_unitRoot_displacement_lt_of_controlSet_near
        X rho z delta hnear j k hjk).le
    _ = (2 * C + 2) * delta := by ring

/-- The same recurrence `C ↦ 2 * C + 2` holds when the initial index is
changed. -/
theorem norm_integral_change_source_displacement_le
    (X : Type u) [Fintype X]
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (rho : elementaryGroup (Fin 3) (FreeAlgebra ℤ X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) (delta C : ℝ)
    (hnear : ∀ s ∈ integralControlSet X, ‖rho s z - z‖ < delta)
    (k i j : Fin 3) (hki : k ≠ i) (hij : i ≠ j) (hkj : k ≠ j)
    (a : FreeAlgebra ℤ X)
    (ha : ‖rho (elementaryRoot i j hij a) z - z‖ ≤ C * delta) :
    ‖rho (elementaryRoot k j hkj a) z - z‖ ≤
      (2 * C + 2) * delta := by
  calc
    ‖rho (elementaryRoot k j hkj a) z - z‖ ≤
        2 * ‖rho (elementaryRoot k i hki 1) z - z‖ +
          2 * ‖rho (elementaryRoot i j hij a) z - z‖ :=
      norm_elementaryRoot_change_source_displacement_le
        rho z k i j hki hij hkj a
    _ ≤ 2 * delta + 2 * (C * delta) := by
      gcongr
      exact (norm_integral_unitRoot_displacement_lt_of_controlSet_near
        X rho z delta hnear k i hki).le
    _ = (2 * C + 2) * delta := by ring

/-- Near invariance under the integral control set includes near invariance
under every free-generator coefficient in every elementary root. -/
theorem norm_integral_generatorRoot_displacement_lt_of_controlSet_near
    (X : Type u) [Fintype X]
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (rho : elementaryGroup (Fin 3) (FreeAlgebra ℤ X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) (delta : ℝ)
    (hnear : ∀ s ∈ integralControlSet X, ‖rho s z - z‖ < delta)
    (i j : Fin 3) (hij : i ≠ j) (x : X) :
    ‖rho (elementaryRoot i j hij (FreeAlgebra.ι ℤ x)) z - z‖ < delta := by
  let a : A2Root := ⟨(i, j), hij⟩
  let p : A2Root × Option X := (a, some x)
  have hp := hnear (integralControlElement X p)
    (integralControlElement_mem X p)
  simpa [p, a, integralControlElement, integralControlCoefficient] using hp

/-- The commutator recursion applied directly to the integral control set.
It controls a word-monomial root, but its constant grows exponentially with
the word length and therefore does not give
`RootCoefficientDisplacementBound`. -/
theorem norm_integral_wordMonomial_displacement_le_of_controlSet_near
    (X : Type u) [Fintype X]
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (rho : elementaryGroup (Fin 3) (FreeAlgebra ℤ X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) (delta : ℝ)
    (hnear : ∀ s ∈ integralControlSet X, ‖rho s z - z‖ < delta)
    (w : FreeMonoid X) (i j : Fin 3) (hij : i ≠ j) :
    ‖rho (elementaryRoot i j hij
        (FreeAlgebraDegree.wordMonomial X ℤ w)) z - z‖ ≤
      (3 * 2 ^ (FreeAlgebraDegree.freeWordLength X w) - 2) * delta := by
  exact norm_displacement_wordMonomial_le X ℤ rho z delta
    (fun i j hij ↦
      (norm_integral_unitRoot_displacement_lt_of_controlSet_near
        X rho z delta hnear i j hij).le)
    (fun i j hij x ↦
      (norm_integral_generatorRoot_displacement_lt_of_controlSet_near
        X rho z delta hnear i j hij x).le)
    w i j hij

end IntegralColumnPlaneRootReduction

end GroupApproximation
