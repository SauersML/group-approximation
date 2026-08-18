import GroupApproximation.Analysis.AbstractSpectralGap
import GroupApproximation.Analysis.CStarSpectralProjection
import GroupApproximation.Analysis.KazhdanProjectionAbsorption
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.StarOrder

/-!
# A vector fixed by the average of unitaries is fixed by each of them

`\label{thm:normal-kazhdan}` says of the spectral projection `P = χ_{{1}}(h)`
that its range is `Fix π(K̄)`.  One of the two inclusions is a fact about
Hilbert spaces and averages of unitaries and has nothing to do with
ultraproducts:

> if `h x = x` for `h = card(S)⁻¹ Σ_{a∈S} π(a)` and each `π(a)` is unitary, then
> `π(a) x = x` for every `a ∈ S`.

This file proves it, and then reads it off the range of the spectral
projection, whose defining property is the absorption `h P = P`.

## The argument

Averaging the inner products against `x` and taking real parts turns `h x = x`
into

`‖x‖² = card(S)⁻¹ Σ_{a∈S} Re⟪x, π(a) x⟫`,

and Cauchy--Schwarz with `‖π(a) x‖ = ‖x‖` bounds every summand by `‖x‖²`.  A
mean of terms each at most `‖x‖²` equals `‖x‖²` only if every term does, so
`Re⟪x, π(a) x⟫ = ‖x‖²` for each `a`, and then

`‖π(a) x − x‖² = ‖π(a) x‖² − 2 Re⟪x, π(a) x⟫ + ‖x‖² = 0`.

No spectral theory and no completeness enter; the only input beyond the Hilbert
structure is that each `π(a)` preserves the norm.

## Where this sits

This is the `ran P ⊆ Fix` half of `NK.06`.  The converse inclusion needs the
functional calculus to see eigenvectors — `h x = x` with `1` isolated above the
gap should give `P x = x` — and is not here.  Neither is the nonvanishing of
`q = 1 − P`, which is a separate argument about the operator-norm separation.
-/

namespace GroupApproximation
namespace UnitaryAverageFixedVector

open AbstractSpectralGap

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] {G : Type*} [Group G]

/-- A unitary of `B(E)` preserves the norm. -/
theorem norm_unitary_apply (u : unitary (E →L[ℂ] E)) (x : E) :
    ‖(u : E →L[ℂ] E) x‖ = ‖x‖ :=
  Unitary.norm_map u x

/-- The average, applied to a vector. -/
theorem unitaryAverage_apply (ρ : G →* unitary (E →L[ℂ] E)) (S : Finset G)
    (x : E) :
    (unitaryAverage ρ S : E →L[ℂ] E) x
      = ((S.card : ℂ))⁻¹ • ∑ g ∈ S, ((ρ g : unitary (E →L[ℂ] E)) : E →L[ℂ] E) x := by
  show (((S.card : ℂ))⁻¹ • ∑ g ∈ S,
      ((ρ g : unitary (E →L[ℂ] E)) : E →L[ℂ] E)) x = _
  rw [smul_apply, sum_apply]

/-- **Equality in the averaged Cauchy--Schwarz.**  A vector fixed by the average
of a finite family of unitaries is fixed by each of them. -/
theorem forall_apply_eq_of_unitaryAverage_apply_eq
    (ρ : G →* unitary (E →L[ℂ] E)) {S : Finset G} (hS : S.Nonempty) {x : E}
    (hx : (unitaryAverage ρ S : E →L[ℂ] E) x = x) :
    ∀ g ∈ S, ((ρ g : unitary (E →L[ℂ] E)) : E →L[ℂ] E) x = x := by
  classical
  set u : G → E →L[ℂ] E := fun g ↦ ((ρ g : unitary (E →L[ℂ] E)) : E →L[ℂ] E) with hu
  have hcard : (0 : ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr hS
  have hnorm : ∀ g : G, ‖u g x‖ = ‖x‖ := fun g ↦ norm_unitary_apply (ρ g) x
  -- The real part of each summand is bounded by `‖x‖²`.
  have hle : ∀ g : G, RCLike.re (inner ℂ x (u g x)) ≤ ‖x‖ ^ 2 := by
    intro g
    have h1 : RCLike.re (inner ℂ x (u g x)) ≤ ‖(inner ℂ x (u g x) : ℂ)‖ :=
      RCLike.re_le_norm _
    have h2 : ‖(inner ℂ x (u g x) : ℂ)‖ ≤ ‖x‖ * ‖u g x‖ := norm_inner_le_norm _ _
    rw [hnorm g] at h2
    calc RCLike.re (inner ℂ x (u g x)) ≤ ‖x‖ * ‖x‖ := le_trans h1 h2
      _ = ‖x‖ ^ 2 := by ring
  -- The average of the real parts is exactly `‖x‖²`.
  have hsum : ∑ g ∈ S, RCLike.re (inner ℂ x (u g x)) = S.card * ‖x‖ ^ 2 := by
    -- Rewrite `x` only in the SECOND slot: `conv_lhs => rw [← hx]` would put the
    -- average in both, and `inner_sum` would then distribute over a sum whose
    -- first argument still carried it.
    have hinner : (inner ℂ x x : ℂ)
        = ((S.card : ℂ))⁻¹ * ∑ g ∈ S, (inner ℂ x (u g x) : ℂ) :=
      calc (inner ℂ x x : ℂ)
          = inner ℂ x ((unitaryAverage ρ S : E →L[ℂ] E) x) := by rw [hx]
        _ = ((S.card : ℂ))⁻¹ * ∑ g ∈ S, (inner ℂ x (u g x) : ℂ) := by
            rw [unitaryAverage_apply ρ S x, inner_smul_right, inner_sum]
    have hcardne : ((S.card : ℂ)) ≠ 0 := by
      simpa using (Nat.cast_ne_zero (R := ℂ)).2 (Finset.card_ne_zero_of_mem hS.choose_spec)
    have hmul : ((S.card : ℂ)) * (inner ℂ x x : ℂ)
        = ∑ g ∈ S, (inner ℂ x (u g x) : ℂ) := by
      rw [hinner, ← mul_assoc, mul_inv_cancel₀ hcardne, one_mul]
    have hcast : ((S.card : ℂ)) * (inner ℂ x x : ℂ)
        = (((S.card : ℝ) * ‖x‖ ^ 2 : ℝ) : ℂ) := by
      -- `inner_self_eq_norm_sq_to_K` coerces through `RCLike.ofReal` and the
      -- ascription through `Complex.ofReal`; the two are definitionally equal
      -- but not syntactically, so `rw` cannot finish and `rfl` can.
      rw [inner_self_eq_norm_sq_to_K, Complex.ofReal_mul, Complex.ofReal_pow,
        Complex.ofReal_natCast]
      rfl
    rw [hcast] at hmul
    have hre := congrArg RCLike.re hmul
    rw [map_sum] at hre
    have hofr : RCLike.re ((((S.card : ℝ) * ‖x‖ ^ 2 : ℝ) : ℂ))
        = (S.card : ℝ) * ‖x‖ ^ 2 := Complex.ofReal_re _
    rw [hofr] at hre
    exact hre.symm
  -- A mean of terms each at most `‖x‖²` that equals `‖x‖²` has every term equal.
  have heq : ∀ g ∈ S, RCLike.re (inner ℂ x (u g x)) = ‖x‖ ^ 2 := by
    intro g hg
    by_contra hne
    have hlt : RCLike.re (inner ℂ x (u g x)) < ‖x‖ ^ 2 := lt_of_le_of_ne (hle g) hne
    have hstrict : ∑ a ∈ S, RCLike.re (inner ℂ x (u a x))
        < ∑ _a ∈ S, ‖x‖ ^ 2 :=
      Finset.sum_lt_sum (fun a _ ↦ hle a) ⟨g, hg, hlt⟩
    rw [hsum, Finset.sum_const, nsmul_eq_mul] at hstrict
    exact lt_irrefl _ hstrict
  -- Equality in Cauchy--Schwarz for an isometry means the vector is fixed.
  intro g hg
  have hsymmre : RCLike.re (inner ℂ (u g x) x) = RCLike.re (inner ℂ x (u g x)) := by
    have hcj : (inner ℂ (u g x) x : ℂ)
        = (starRingEnd ℂ) (inner ℂ x (u g x)) :=
      (inner_conj_symm (𝕜 := ℂ) (u g x) x).symm
    rw [hcj]
    exact RCLike.conj_re _
  have hzero : ‖u g x - x‖ ^ 2 = 0 := by
    rw [norm_sub_sq (𝕜 := ℂ) (u g x) x, hsymmre, hnorm g, heq g hg]
    ring
  have : u g x - x = 0 := by
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hzero
    exact norm_eq_zero.mp this
  exact sub_eq_zero.mp this

/-- **The range of the spectral projection is fixed pointwise.**

`CStarSpectralProjection.mul_spectralProjection` is the printed absorption
`h P = P`, so every vector in the range of `P` is fixed by `h`, and the lemma
above then fixes it under every `π(a)`.  This is the `ran P ⊆ Fix π` half of
`NK.06`, at the Kazhdan set; membership in `Fix π` for the whole group follows
because `S` generates it in the printed setting. -/
theorem forall_apply_eq_of_spectralProjection
    (ρ : G →* unitary (E →L[ℂ] E)) {S : Finset G} (hS : S.Nonempty)
    (hsymm : ∀ g ∈ S, g⁻¹ ∈ S) {c : ℝ} (hc : c < 1)
    (hgap : ∀ μ ∈ spectrum ℝ (unitaryAverage ρ S), μ ≤ c ∨ μ = 1)
    (y : E) (g : G) (hg : g ∈ S) :
    ((ρ g : unitary (E →L[ℂ] E)) : E →L[ℂ] E)
        ((CStarSpectralProjection.spectralProjection (unitaryAverage ρ S) c :
          E →L[ℂ] E) y)
      = (CStarSpectralProjection.spectralProjection (unitaryAverage ρ S) c :
          E →L[ℂ] E) y := by
  set m := unitaryAverage ρ S with hm
  set P := CStarSpectralProjection.spectralProjection m c with hP
  have hsa : IsSelfAdjoint m := isSelfAdjoint_unitaryAverage ρ hsymm
  have habs : m * P = P := CStarSpectralProjection.mul_spectralProjection m hsa hc hgap
  have hfix : (m : E →L[ℂ] E) ((P : E →L[ℂ] E) y) = (P : E →L[ℂ] E) y := by
    have := congrArg (fun T : E →L[ℂ] E ↦ T y) habs
    simpa using this
  exact forall_apply_eq_of_unitaryAverage_apply_eq ρ hS hfix g hg

/-- The average fixes a vector that every member of the set fixes. -/
theorem unitaryAverage_apply_eq_self
    (ρ : G →* unitary (E →L[ℂ] E)) {S : Finset G} (hS : S.Nonempty) {x : E}
    (hx : ∀ g ∈ S, ((ρ g : unitary (E →L[ℂ] E)) : E →L[ℂ] E) x = x) :
    (unitaryAverage ρ S : E →L[ℂ] E) x = x := by
  classical
  have hcardne : ((S.card : ℂ)) ≠ 0 := by
    simpa using (Nat.cast_ne_zero (R := ℂ)).2 (Finset.card_ne_zero_of_mem hS.choose_spec)
  rw [unitaryAverage_apply ρ S x]
  have hsum : ∑ g ∈ S, ((ρ g : unitary (E →L[ℂ] E)) : E →L[ℂ] E) x
      = ((S.card : ℂ)) • x := by
    rw [Finset.sum_congr rfl fun g hg ↦ hx g hg, Finset.sum_const]
    exact (Nat.cast_smul_eq_nsmul ℂ S.card x).symm
  rw [hsum, smul_smul, inv_mul_cancel₀ hcardne, one_smul]

/-- **`Fix ⊆ ran P`, the converse inclusion.**

The printed `P = χ_{{1}}(h)` "projects onto `Fix`" has two halves.  The other one
is above; this is the one that consumes the spectral gap, through the resolvent
factorisation `1 − P = cfc (gapResolvent c) h · (1 − h)` of
`KazhdanProjectionAbsorption.one_sub_spectralProjection_eq`.  A vector fixed by
every `π(a)` is fixed by `h`, so `(1 − h) x = 0`, so `(1 − P) x = 0`.

Note where the gap is spent: not in this calculation, which is one application of
a factorisation, but in the factorisation's own hypothesis that the spectrum
meets `(c, ∞)` only in `{1}` — which is what makes `gapResolvent c` continuous on
the spectrum and the functional calculus available at all. -/
theorem spectralProjection_apply_eq_of_forall_apply_eq
    (ρ : G →* unitary (E →L[ℂ] E)) {S : Finset G} (hS : S.Nonempty)
    (hsymm : ∀ g ∈ S, g⁻¹ ∈ S) {c : ℝ} (hc : c < 1)
    (hgap : ∀ μ ∈ spectrum ℝ (unitaryAverage ρ S), μ ≤ c ∨ μ = 1)
    {x : E} (hx : ∀ g ∈ S, ((ρ g : unitary (E →L[ℂ] E)) : E →L[ℂ] E) x = x) :
    (CStarSpectralProjection.spectralProjection (unitaryAverage ρ S) c :
      E →L[ℂ] E) x = x := by
  set m := unitaryAverage ρ S with hm
  have hsa : IsSelfAdjoint m := isSelfAdjoint_unitaryAverage ρ hsymm
  have hmx : (m : E →L[ℂ] E) x = x := unitaryAverage_apply_eq_self ρ hS hx
  have hfac : (1 : E →L[ℂ] E) - CStarSpectralProjection.spectralProjection m c
      = cfc (KazhdanProjectionAbsorption.gapResolvent c) m * ((1 : E →L[ℂ] E) - m) :=
    KazhdanProjectionAbsorption.one_sub_spectralProjection_eq m hsa hc hgap
  have hzero : ((1 : E →L[ℂ] E) - m) x = 0 := by
    simp [hmx]
  have happ := congrArg (fun T : E →L[ℂ] E ↦ T x) hfac
  simp only [sub_apply, one_apply_eq_self, mul_apply_eq_comp, hzero, map_zero] at happ
  exact (sub_eq_zero.mp happ).symm

/-- **`ran P = Fix`, as the printed sentence.**

> the spectral projection `P` of `h` at the isolated point `1` … projects onto
> `Fix`.

A vector is fixed by `P` exactly when it is fixed by every member of the Kazhdan
set.  Left to right is the equality case of Cauchy--Schwarz through the
absorption `h P = P`; right to left is the resolvent factorisation of `1 − P`,
and it is where the gap is spent. -/
theorem spectralProjection_apply_eq_self_iff
    (ρ : G →* unitary (E →L[ℂ] E)) {S : Finset G} (hS : S.Nonempty)
    (hsymm : ∀ g ∈ S, g⁻¹ ∈ S) {c : ℝ} (hc : c < 1)
    (hgap : ∀ μ ∈ spectrum ℝ (unitaryAverage ρ S), μ ≤ c ∨ μ = 1) (x : E) :
    (CStarSpectralProjection.spectralProjection (unitaryAverage ρ S) c :
        E →L[ℂ] E) x = x
      ↔ ∀ g ∈ S, ((ρ g : unitary (E →L[ℂ] E)) : E →L[ℂ] E) x = x := by
  constructor
  · intro hPx g hg
    have h := forall_apply_eq_of_spectralProjection ρ hS hsymm hc hgap x g hg
    rwa [hPx] at h
  · exact spectralProjection_apply_eq_of_forall_apply_eq ρ hS hsymm hc hgap

end

end UnitaryAverageFixedVector
end GroupApproximation
