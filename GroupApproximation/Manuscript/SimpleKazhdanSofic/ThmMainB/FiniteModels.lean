import GroupApproximation.Manuscript.SimpleKazhdanSofic.FiniteModelsAsymptotic
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Setting
import GroupApproximation.Meta.AxiomGuard

/-!
# `thm:main`, proof sketch: the finite models ingredient

`simple_kazhdan_sofic_group.tex`, l.125–129:

> \emph{Finite models.} A periodic sequence of period $N$ approximating $X$ turns the shift into a
> cyclic permutation matrix and each locally constant function into a diagonal matrix
> (Figure~\ref{fig:models}(a)), as in the proof by Grigorchuk and Medynets that topological full
> groups of minimal Cantor systems are LEF~\cite[Theorem~2.6]{GM}.

The periodic sequences are `y_ℓ = periodicExt x (m ℓ)` (a recurrence block of a point `x ∈ X`
repeated), of least period `N_ℓ`, with the same words of length `2ℓ + 1` as `X` ("approximating
`X`"), and `N_ℓ → ∞`.  The model `φ_ℓ = Pestov91.periodicModel (D ℓ) : R S →+ M_{N_ℓ}(F₂)` sends
`u^j` to the cyclic permutation matrix `δ_b ↦ δ_{b + j}` on `ℤ/N_ℓ`, and `coeff f` to the diagonal
matrix `diag (D_ℓ f)`, where `D_ℓ f (t) = f z` for any `z ∈ X` agreeing with `y_ℓ` shifted by `t`
on the window `[-ℓ, ℓ]` on which `f` depends.  These models are eventually multiplicative on every
pair `r, s`.  All of this is the absorbed, closed `exists_asymptoticModels` (in-repo proof; the
Grigorchuk--Medynets citation is "as in", i.e. the same construction, not an input).

* `periodicModel_unit_zpow_apply`, `periodicModel_coeff`: the two matrix formulas;
* `manuscriptSentence_periodicModelsShiftPermutationDiagonal`: the sentence.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic
namespace ThmMainB

open SymbolicDynamics.FullShift WordGraph Filter

/-- The periodic model sends `u^j` to the cyclic permutation matrix `δ_b ↦ δ_{b+j}` on `ℤ/N`. -/
theorem periodicModel_unit_zpow_apply {A : Type} [TopologicalSpace A] (S : Subshift A ℤ)
    {N : ℕ} [NeZero N] (D : ClopenCoeff (subshiftHomeo S) (ZMod 2) →+* (ZMod N → ZMod 2)) (j : ℤ)
    (a b : ZMod N) :
    Pestov91.periodicModel D
        ((ClopenCrossedProduct.unit (subshiftHomeo S) (ZMod 2) ^ j : (R S)ˣ) : R S) a b =
      if b + (j : ZMod N) = a then 1 else 0 := by
  rw [Pestov91.CrossedProduct.val_unit_zpow, Pestov91.periodicModel_single, map_one,
    show Matrix.diagonal (1 : ZMod N → ZMod 2) = 1 from Matrix.diagonal_one, one_mul, toAdd_ofAdd,
    Pestov91.shiftMatrix_apply]

/-- The periodic model sends a locally constant function to a diagonal matrix. -/
theorem periodicModel_coeff {A : Type} [TopologicalSpace A] (S : Subshift A ℤ)
    {N : ℕ} [NeZero N] (D : ClopenCoeff (subshiftHomeo S) (ZMod 2) →+* (ZMod N → ZMod 2))
    (f : LocallyConstant S.carrier (ZMod 2)) :
    Pestov91.periodicModel D (ClopenCrossedProduct.coeff (subshiftHomeo S) (ZMod 2) f) =
      Matrix.diagonal (D (ClopenCoeff.of (subshiftHomeo S) (ZMod 2) f)) := by
  rw [ClopenCrossedProduct.coeff_apply, Pestov91.CrossedProduct.C_apply,
    Pestov91.periodicModel_single, toAdd_one, Pestov91.shiftMatrix_zero, mul_one]

/-- **tex l.125–129.** For an infinite minimal subshift `X` over a finite alphabet there are
periodic sequences `y_ℓ` of (least) period `N_ℓ → ∞` approximating `X` (same words of length
`2ℓ + 1`), and additive maps `φ_ℓ : LC(X, F₂) ⋊_T ℤ → M_{N_ℓ}(F₂)` turning the shift `u^j` into
the cyclic permutation matrix `δ_b ↦ δ_{b+j}` and each locally constant `f` into the diagonal
matrix `diag (D_ℓ f)`, whose entry at `t` is the value of `f` at a point agreeing with the `t`-th
shift of `y_ℓ` on the window of `f`; the maps are eventually multiplicative on every pair. -/
theorem manuscriptSentence_periodicModelsShiftPermutationDiagonal (A : Type) [TopologicalSpace A]
    [DiscreteTopology A] [Finite A] (S : Subshift A ℤ) (hinf : Infinite S.carrier)
    (hmin : IsMinimal S) :
    ∃ (y : ℕ → ℤ → A) (N : ℕ → ℕ) (_ : ∀ ℓ, NeZero (N ℓ))
      (D : ∀ ℓ, LocallyConstant S.carrier (ZMod 2) →+* (ZMod (N ℓ) → ZMod 2))
      (φ : ∀ ℓ, R S →+ Matrix (ZMod (N ℓ)) (ZMod (N ℓ)) (ZMod 2)),
      (∀ ℓ, N ℓ = leastPeriod (y ℓ) ∧ (∀ t : ℤ, y ℓ ((N ℓ : ℤ) + t) = y ℓ t) ∧
        {w | ∃ t : ℤ, word (y ℓ) t (2 * ℓ + 1) = w} = language S.carrier (2 * ℓ + 1)) ∧
      Tendsto N atTop atTop ∧
      (∀ (ℓ : ℕ) (j : ℤ) (a b : ZMod (N ℓ)),
        φ ℓ ((ClopenCrossedProduct.unit (subshiftHomeo S) (ZMod 2) ^ j : (R S)ˣ) : R S) a b =
          if b + (j : ZMod (N ℓ)) = a then 1 else 0) ∧
      (∀ (ℓ : ℕ) (f : LocallyConstant S.carrier (ZMod 2)),
        φ ℓ (ClopenCrossedProduct.coeff (subshiftHomeo S) (ZMod 2) f) = Matrix.diagonal (D ℓ f)) ∧
      (∀ (ℓ : ℕ) (f : LocallyConstant S.carrier (ZMod 2)),
        (∀ z z' : S.carrier, (∀ i : ℤ, |i| ≤ ℓ → z.1 i = z'.1 i) → f z = f z') →
        ∀ (t : ℤ) (z : S.carrier), (∀ i : ℤ, |i| ≤ ℓ → z.1 i = y ℓ (t + i)) →
          D ℓ f (t : ZMod (N ℓ)) = f z) ∧
      ∀ r s : R S, ∀ᶠ ℓ in atTop, φ ℓ (r * s) = φ ℓ r * φ ℓ s := by
  classical
  obtain ⟨⟨x, hx⟩⟩ := hinf.nonempty
  obtain ⟨m, N, hNz, D, hwords, hform, -, hN, hmul⟩ :=
    exists_asymptoticModels S.isClosed S.mapsTo (Set.infinite_coe_iff.1 hinf) hmin (subshiftHomeo S)
      (fun _ => rfl) hx (ZMod 2)
  haveI : ∀ ℓ, NeZero (N ℓ) := hNz
  have hper : ∀ (ℓ : ℕ) (t : ℤ), periodicExt x (m ℓ) (N ℓ + t) = periodicExt x (m ℓ) t :=
    fun ℓ t => by
      rw [(hwords ℓ).2.2.1]
      exact periodicExt_leastPeriod_add x (m ℓ) t
  have hwin : ∀ (ℓ : ℕ) (f : LocallyConstant S.carrier (ZMod 2)),
      (∀ z z' : S.carrier, (∀ i : ℤ, |i| ≤ ℓ → z.1 i = z'.1 i) → f z = f z') →
      ∀ (t : ℤ) (z : S.carrier), (∀ i : ℤ, |i| ≤ ℓ → z.1 i = periodicExt x (m ℓ) (t + i)) →
        D ℓ (ClopenCoeff.of (subshiftHomeo S) (ZMod 2) f) (t : ZMod (N ℓ)) = f z := by
    intro ℓ f hf t z hz
    have h := hform ℓ (ClopenCoeff.of (subshiftHomeo S) (ZMod 2) f)
      (fun z₁ z₂ h₁₂ => by
        simp only [RingEquiv.symm_apply_apply]
        exact hf z₁ z₂ h₁₂) t z hz
    simp only [RingEquiv.symm_apply_apply] at h
    exact h
  exact ⟨fun ℓ => periodicExt x (m ℓ), N, hNz,
    fun ℓ => (D ℓ).comp (ClopenCoeff.of (subshiftHomeo S) (ZMod 2)).toRingHom,
    fun ℓ => Pestov91.periodicModel (D ℓ),
    fun ℓ => ⟨(hwords ℓ).2.2.1, hper ℓ, (hwords ℓ).2.2.2⟩, hN,
    fun ℓ j a b => periodicModel_unit_zpow_apply S (D ℓ) j a b,
    fun ℓ f => periodicModel_coeff S (D ℓ) f,
    fun ℓ f hf t z hz => hwin ℓ f hf t z hz, hmul⟩

end ThmMainB
end SimpleKazhdanSofic
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.SimpleKazhdanSofic.ThmMainB.periodicModel_unit_zpow_apply
#audit_axioms GroupApproximation.SimpleKazhdanSofic.ThmMainB.periodicModel_coeff
#audit_axioms GroupApproximation.SimpleKazhdanSofic.ThmMainB.manuscriptSentence_periodicModelsShiftPermutationDiagonal
