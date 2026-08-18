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

/-- **`q = 1 − P` is nonzero exactly when the representation is nontrivial on
the Kazhdan set.**

> `q = 1 − P` is nonzero because `q = 0` would make `π` trivial on `K̄`, against
> the operator-norm separation.

The printed reason, as an iff.  `P = 1` says every vector of the space is fixed
by `P`, and by the range identification that says every vector is fixed by every
`π(a)`, which is exactly triviality of `π` on the Kazhdan set.  So the
nonvanishing of `q` needs no estimate of its own: whatever supplies
nontriviality — in the manuscript, the operator-norm separation — supplies `q ≠
0` through this. -/
theorem one_sub_spectralProjection_ne_zero_iff
    (ρ : G →* unitary (E →L[ℂ] E)) {S : Finset G} (hS : S.Nonempty)
    (hsymm : ∀ g ∈ S, g⁻¹ ∈ S) {c : ℝ} (hc : c < 1)
    (hgap : ∀ μ ∈ spectrum ℝ (unitaryAverage ρ S), μ ≤ c ∨ μ = 1) :
    (1 : E →L[ℂ] E)
        - CStarSpectralProjection.spectralProjection (unitaryAverage ρ S) c ≠ 0
      ↔ ∃ g ∈ S, ((ρ g : unitary (E →L[ℂ] E)) : E →L[ℂ] E) ≠ 1 := by
  set P := CStarSpectralProjection.spectralProjection (unitaryAverage ρ S) c with hP
  have hkey : P = 1 ↔ ∀ g ∈ S, ((ρ g : unitary (E →L[ℂ] E)) : E →L[ℂ] E) = 1 := by
    constructor
    · intro h1 g hg
      refine ContinuousLinearMap.ext fun x ↦ ?_
      have hPx : (P : E →L[ℂ] E) x = x := by rw [h1]; rfl
      have := (spectralProjection_apply_eq_self_iff ρ hS hsymm hc hgap x).1 hPx g hg
      simpa using this
    · intro hall
      refine ContinuousLinearMap.ext fun x ↦ ?_
      have : (P : E →L[ℂ] E) x = x :=
        (spectralProjection_apply_eq_self_iff ρ hS hsymm hc hgap x).2
          (fun g hg ↦ by rw [hall g hg]; rfl)
      simpa using this
  constructor
  · intro hq
    by_contra hall
    push Not at hall
    exact hq (by rw [hkey.2 hall, sub_self])
  · rintro ⟨g, hg, hne⟩ hq
    exact hne (hkey.1 (by
      have : (1 : E →L[ℂ] E) = P := by
        have := sub_eq_zero.mp hq
        exact this
      exact this.symm) g hg)

/-! ## The commutation step, unconditionally

`thm:normal-kazhdan` continues "normality gives `π(g)Pπ(g)* = P`, so `P` and `q`
commute with `π(H̄)` exactly".  Two facts underlie that, and neither needs
normality, ultraproducts, or the Kazhdan gap; normality enters only to supply
the hypothesis of the second.

* a self-adjoint idempotent is determined by the vectors it fixes;
* conjugating one by a unitary conjugates the fixed set.

So the printed step is: normality says `π(g)` preserves `Fix`, hence `π(g)Pπ(g)*`
and `P` fix the same vectors, hence they are equal. -/

section Commutation

/-- **A self-adjoint idempotent is determined by what it fixes.**

Purely algebraic, and shorter than the orthogonal-projection route: if the two
agree on which vectors they fix then `Q P = P`, taking adjoints gives
`P Q = P`, and the symmetric argument gives `P Q = Q`. -/
theorem eq_of_isSelfAdjoint_idempotent_of_fix_iff {P Q : E →L[ℂ] E}
    (hP : IsSelfAdjoint P) (hQ : IsSelfAdjoint Q)
    (hPi : P * P = P) (hQi : Q * Q = Q)
    (hfix : ∀ x : E, P x = x ↔ Q x = x) : P = Q := by
  have hQP : Q * P = P := by
    refine ContinuousLinearMap.ext fun x ↦ ?_
    have hPx : P (P x) = P x := by
      have := congrArg (fun T : E →L[ℂ] E ↦ T x) hPi
      simpa [mul_apply_eq_comp] using this
    have := (hfix (P x)).1 hPx
    simpa [mul_apply_eq_comp] using this
  have hPQ : P * Q = Q := by
    refine ContinuousLinearMap.ext fun x ↦ ?_
    have hQx : Q (Q x) = Q x := by
      have := congrArg (fun T : E →L[ℂ] E ↦ T x) hQi
      simpa [mul_apply_eq_comp] using this
    have := (hfix (Q x)).2 hQx
    simpa [mul_apply_eq_comp] using this
  -- `star (Q * P) = star P * star Q = P * Q`, and the left side is `star P = P`.
  have hstar : P * Q = P := by
    have := congrArg star hQP
    rwa [star_mul, hP.star_eq, hQ.star_eq] at this
  rw [← hstar, hPQ]

/-- **Conjugating by a unitary conjugates the fixed set.** -/
theorem conj_apply_eq_self_iff (u : unitary (E →L[ℂ] E)) (P : E →L[ℂ] E) (x : E) :
    ((u : E →L[ℂ] E) * P * star (u : E →L[ℂ] E)) x = x
      ↔ P ((star (u : E →L[ℂ] E)) x) = (star (u : E →L[ℂ] E)) x := by
  constructor
  · intro h
    have := congrArg (fun y ↦ (star (u : E →L[ℂ] E)) y) h
    simp only [mul_apply_eq_comp] at this ⊢
    have hstar : (star (u : E →L[ℂ] E)) ((u : E →L[ℂ] E)
        (P ((star (u : E →L[ℂ] E)) x))) = P ((star (u : E →L[ℂ] E)) x) := by
      have hu : (star (u : E →L[ℂ] E) * (u : E →L[ℂ] E))
          (P ((star (u : E →L[ℂ] E)) x))
          = (1 : E →L[ℂ] E) (P ((star (u : E →L[ℂ] E)) x)) := by rw [u.2.1]
      exact hu
    rw [hstar] at this
    exact this
  · intro h
    simp only [mul_apply_eq_comp]
    rw [h]
    have hu : ((u : E →L[ℂ] E) * star (u : E →L[ℂ] E)) x
        = (1 : E →L[ℂ] E) x := by rw [u.2.2]
    exact hu

end Commutation

/-! ## Normality, and the printed conjugation identity

`thm:normal-kazhdan` continues:

> For `g ∈ H̄` the projection `π(g)Pπ(g)*` has range `Fix π(gK̄g⁻¹) = Fix π(K̄)`
> by normality, so `P` and `q` commute with `π(H̄)` exactly.

The printed argument is about *ranges*, so it is a statement about vectors and
belongs here rather than in the ambient algebra.  Three steps: a vector fixed by
the Kazhdan set is fixed by the subgroup it generates; normality moves that
fixed set to itself along the representation; and a self-adjoint idempotent is
determined by what it fixes.  The Kazhdan gap enters only through the range
identification, and Dedekind finiteness of the ambient -- the route the
finite-stage development takes -- is not used. -/

section Normality

variable (ρ : G →* unitary (E →L[ℂ] E))

theorem rep_mul_apply (a b : G) (y : E) :
    ((ρ (a * b) : unitary (E →L[ℂ] E)) : E →L[ℂ] E) y
      = ((ρ a : unitary (E →L[ℂ] E)) : E →L[ℂ] E)
          (((ρ b : unitary (E →L[ℂ] E)) : E →L[ℂ] E) y) := by
  rw [map_mul]
  rfl

theorem rep_one_apply (y : E) :
    ((ρ (1 : G) : unitary (E →L[ℂ] E)) : E →L[ℂ] E) y = y := by
  rw [map_one]
  rfl

theorem rep_apply_inv_apply (a : G) (y : E) :
    ((ρ a : unitary (E →L[ℂ] E)) : E →L[ℂ] E)
        (((ρ a⁻¹ : unitary (E →L[ℂ] E)) : E →L[ℂ] E) y) = y := by
  rw [← rep_mul_apply, mul_inv_cancel]
  exact rep_one_apply ρ y

/-- **A vector fixed by every generator is fixed by the subgroup they
generate.**  This is what turns the printed `Fix π(K̄)`, a statement about the
subgroup, into the statement about the Kazhdan set that the range
identification produces. -/
theorem apply_eq_self_of_mem_closure {S : Set G} {x : E}
    (hx : ∀ g ∈ S, ((ρ g : unitary (E →L[ℂ] E)) : E →L[ℂ] E) x = x)
    {k : G} (hk : k ∈ Subgroup.closure S) :
    ((ρ k : unitary (E →L[ℂ] E)) : E →L[ℂ] E) x = x := by
  induction hk using Subgroup.closure_induction with
  | mem a ha => exact hx a ha
  | one => exact rep_one_apply ρ x
  | mul a b _ _ ha hb => rw [rep_mul_apply, hb, ha]
  | inv a _ ha =>
      calc ((ρ a⁻¹ : unitary (E →L[ℂ] E)) : E →L[ℂ] E) x
          = ((ρ a⁻¹ : unitary (E →L[ℂ] E)) : E →L[ℂ] E)
              (((ρ a : unitary (E →L[ℂ] E)) : E →L[ℂ] E) x) := by rw [ha]
        _ = x := by
            have h := rep_apply_inv_apply ρ a⁻¹ x
            rwa [inv_inv] at h

/-- **Normality moves the fixed set of `K` into itself.**  The printed
`Fix π(gK̄g⁻¹) = Fix π(K̄)`, in the direction the induction needs: `π(g)` sends a
vector fixed by `π(K̄)` to another one. -/
theorem forall_apply_eq_self_of_normal {K : Subgroup G}
    (hnorm : ∀ g : G, ∀ k ∈ K, g * k * g⁻¹ ∈ K) {x : E}
    (hx : ∀ k ∈ K, ((ρ k : unitary (E →L[ℂ] E)) : E →L[ℂ] E) x = x) (g : G) :
    ∀ k ∈ K, ((ρ k : unitary (E →L[ℂ] E)) : E →L[ℂ] E)
        (((ρ g : unitary (E →L[ℂ] E)) : E →L[ℂ] E) x)
      = ((ρ g : unitary (E →L[ℂ] E)) : E →L[ℂ] E) x := by
  intro k hk
  have hk' : g⁻¹ * k * g ∈ K := by
    have h := hnorm g⁻¹ k hk
    rwa [inv_inv] at h
  calc ((ρ k : unitary (E →L[ℂ] E)) : E →L[ℂ] E)
        (((ρ g : unitary (E →L[ℂ] E)) : E →L[ℂ] E) x)
      = ((ρ (k * g) : unitary (E →L[ℂ] E)) : E →L[ℂ] E) x :=
        (rep_mul_apply ρ k g x).symm
    _ = ((ρ (g * (g⁻¹ * k * g)) : unitary (E →L[ℂ] E)) : E →L[ℂ] E) x := by
        rw [show k * g = g * (g⁻¹ * k * g) by group]
    _ = ((ρ g : unitary (E →L[ℂ] E)) : E →L[ℂ] E)
          (((ρ (g⁻¹ * k * g) : unitary (E →L[ℂ] E)) : E →L[ℂ] E) x) :=
        rep_mul_apply ρ g (g⁻¹ * k * g) x
    _ = ((ρ g : unitary (E →L[ℂ] E)) : E →L[ℂ] E) x := by rw [hx _ hk']

/-- **The fixed set of a normal subgroup is translation invariant**, which is
the printed equality `Fix π(gK̄g⁻¹) = Fix π(K̄)` in both directions. -/
theorem forall_apply_eq_self_translate_iff {K : Subgroup G}
    (hnorm : ∀ g : G, ∀ k ∈ K, g * k * g⁻¹ ∈ K) (g : G) (x : E) :
    (∀ k ∈ K, ((ρ k : unitary (E →L[ℂ] E)) : E →L[ℂ] E)
        (((ρ g : unitary (E →L[ℂ] E)) : E →L[ℂ] E) x)
      = ((ρ g : unitary (E →L[ℂ] E)) : E →L[ℂ] E) x)
      ↔ ∀ k ∈ K, ((ρ k : unitary (E →L[ℂ] E)) : E →L[ℂ] E) x = x := by
  constructor
  · intro h
    have hgg : ((ρ g⁻¹ : unitary (E →L[ℂ] E)) : E →L[ℂ] E)
        (((ρ g : unitary (E →L[ℂ] E)) : E →L[ℂ] E) x) = x := by
      have hx := rep_apply_inv_apply ρ g⁻¹ x
      rwa [inv_inv] at hx
    have h2 := forall_apply_eq_self_of_normal ρ hnorm h g⁻¹
    intro k hk
    have h3 := h2 k hk
    rwa [hgg] at h3
  · intro h
    exact forall_apply_eq_self_of_normal ρ hnorm h g

/-- **`NK.07`, first clause, on the printed objects.**

> normality gives `π(g)Pπ(g)* = P`, so `P` and `q` commute with `π(H̄)` exactly.

The hypothesis `hnorm` is the printed `gK̄g⁻¹ = K̄` with `K̄` the subgroup
generated by the Kazhdan set, which is the printed `K̄` -- the print takes `S`
to be a *generating* Kazhdan set of `K̄`. -/
theorem conj_spectralProjection_eq {S : Finset G} (hS : S.Nonempty)
    (hsymm : ∀ g ∈ S, g⁻¹ ∈ S) {c : ℝ} (hc : c < 1)
    (hgap : ∀ μ ∈ spectrum ℝ (unitaryAverage ρ S), μ ≤ c ∨ μ = 1)
    (hnorm : ∀ g : G, ∀ k ∈ Subgroup.closure (S : Set G),
      g * k * g⁻¹ ∈ Subgroup.closure (S : Set G))
    (g : G) :
    ((ρ g : unitary (E →L[ℂ] E)) : E →L[ℂ] E)
        * CStarSpectralProjection.spectralProjection (unitaryAverage ρ S) c
        * star ((ρ g : unitary (E →L[ℂ] E)) : E →L[ℂ] E)
      = CStarSpectralProjection.spectralProjection (unitaryAverage ρ S) c := by
  have hsa : IsSelfAdjoint (unitaryAverage ρ S) :=
    isSelfAdjoint_unitaryAverage ρ hsymm
  have hPsa : IsSelfAdjoint
      (CStarSpectralProjection.spectralProjection (unitaryAverage ρ S) c) :=
    CStarSpectralProjection.isSelfAdjoint_spectralProjection _
  have hPi : CStarSpectralProjection.spectralProjection (unitaryAverage ρ S) c
      * CStarSpectralProjection.spectralProjection (unitaryAverage ρ S) c
      = CStarSpectralProjection.spectralProjection (unitaryAverage ρ S) c :=
    CStarSpectralProjection.isIdempotentElem_spectralProjection _ hsa hc hgap
  have hus : star ((ρ g : unitary (E →L[ℂ] E)) : E →L[ℂ] E)
      * ((ρ g : unitary (E →L[ℂ] E)) : E →L[ℂ] E) = 1 := (ρ g).2.1
  have hQsa : IsSelfAdjoint (((ρ g : unitary (E →L[ℂ] E)) : E →L[ℂ] E)
      * CStarSpectralProjection.spectralProjection (unitaryAverage ρ S) c
      * star ((ρ g : unitary (E →L[ℂ] E)) : E →L[ℂ] E)) := by
    rw [IsSelfAdjoint, star_mul, star_mul, star_star, hPsa.star_eq, ← mul_assoc]
  have hQi : (((ρ g : unitary (E →L[ℂ] E)) : E →L[ℂ] E)
        * CStarSpectralProjection.spectralProjection (unitaryAverage ρ S) c
        * star ((ρ g : unitary (E →L[ℂ] E)) : E →L[ℂ] E))
      * (((ρ g : unitary (E →L[ℂ] E)) : E →L[ℂ] E)
        * CStarSpectralProjection.spectralProjection (unitaryAverage ρ S) c
        * star ((ρ g : unitary (E →L[ℂ] E)) : E →L[ℂ] E))
      = ((ρ g : unitary (E →L[ℂ] E)) : E →L[ℂ] E)
        * CStarSpectralProjection.spectralProjection (unitaryAverage ρ S) c
        * star ((ρ g : unitary (E →L[ℂ] E)) : E →L[ℂ] E) := by
    calc (((ρ g : unitary (E →L[ℂ] E)) : E →L[ℂ] E)
            * CStarSpectralProjection.spectralProjection (unitaryAverage ρ S) c
            * star ((ρ g : unitary (E →L[ℂ] E)) : E →L[ℂ] E))
          * (((ρ g : unitary (E →L[ℂ] E)) : E →L[ℂ] E)
            * CStarSpectralProjection.spectralProjection (unitaryAverage ρ S) c
            * star ((ρ g : unitary (E →L[ℂ] E)) : E →L[ℂ] E))
        = ((ρ g : unitary (E →L[ℂ] E)) : E →L[ℂ] E)
            * CStarSpectralProjection.spectralProjection (unitaryAverage ρ S) c
            * (star ((ρ g : unitary (E →L[ℂ] E)) : E →L[ℂ] E)
              * ((ρ g : unitary (E →L[ℂ] E)) : E →L[ℂ] E))
            * CStarSpectralProjection.spectralProjection (unitaryAverage ρ S) c
            * star ((ρ g : unitary (E →L[ℂ] E)) : E →L[ℂ] E) := by
          noncomm_ring
      _ = ((ρ g : unitary (E →L[ℂ] E)) : E →L[ℂ] E)
            * (CStarSpectralProjection.spectralProjection (unitaryAverage ρ S) c
              * CStarSpectralProjection.spectralProjection
                (unitaryAverage ρ S) c)
            * star ((ρ g : unitary (E →L[ℂ] E)) : E →L[ℂ] E) := by
          rw [hus]
          noncomm_ring
      _ = ((ρ g : unitary (E →L[ℂ] E)) : E →L[ℂ] E)
            * CStarSpectralProjection.spectralProjection (unitaryAverage ρ S) c
            * star ((ρ g : unitary (E →L[ℂ] E)) : E →L[ℂ] E) := by rw [hPi]
  have hstar : star ((ρ g : unitary (E →L[ℂ] E)) : E →L[ℂ] E)
      = ((ρ g⁻¹ : unitary (E →L[ℂ] E)) : E →L[ℂ] E) := star_unitary_coe ρ g
  have hfix : ∀ x : E,
      (((ρ g : unitary (E →L[ℂ] E)) : E →L[ℂ] E)
          * CStarSpectralProjection.spectralProjection (unitaryAverage ρ S) c
          * star ((ρ g : unitary (E →L[ℂ] E)) : E →L[ℂ] E)) x = x
        ↔ (CStarSpectralProjection.spectralProjection (unitaryAverage ρ S) c :
            E →L[ℂ] E) x = x := by
    intro x
    rw [conj_apply_eq_self_iff (ρ g) _ x, hstar,
      spectralProjection_apply_eq_self_iff ρ hS hsymm hc hgap,
      spectralProjection_apply_eq_self_iff ρ hS hsymm hc hgap]
    constructor
    · intro h a ha
      exact (forall_apply_eq_self_translate_iff ρ hnorm g⁻¹ x).1
        (fun k hk ↦ apply_eq_self_of_mem_closure ρ h hk) a
        (Subgroup.subset_closure (Finset.mem_coe.2 ha))
    · intro h a ha
      exact (forall_apply_eq_self_translate_iff ρ hnorm g⁻¹ x).2
        (fun k hk ↦ apply_eq_self_of_mem_closure ρ h hk) a
        (Subgroup.subset_closure (Finset.mem_coe.2 ha))
  exact eq_of_isSelfAdjoint_idempotent_of_fix_iff hQsa hPsa hQi hPi hfix

/-- **`P` commutes with `π(g)`**, the form the printed sentence draws from the
conjugation identity. -/
theorem commute_spectralProjection {S : Finset G} (hS : S.Nonempty)
    (hsymm : ∀ g ∈ S, g⁻¹ ∈ S) {c : ℝ} (hc : c < 1)
    (hgap : ∀ μ ∈ spectrum ℝ (unitaryAverage ρ S), μ ≤ c ∨ μ = 1)
    (hnorm : ∀ g : G, ∀ k ∈ Subgroup.closure (S : Set G),
      g * k * g⁻¹ ∈ Subgroup.closure (S : Set G))
    (g : G) :
    ((ρ g : unitary (E →L[ℂ] E)) : E →L[ℂ] E)
        * CStarSpectralProjection.spectralProjection (unitaryAverage ρ S) c
      = CStarSpectralProjection.spectralProjection (unitaryAverage ρ S) c
        * ((ρ g : unitary (E →L[ℂ] E)) : E →L[ℂ] E) := by
  have hconj := conj_spectralProjection_eq ρ hS hsymm hc hgap hnorm g
  have hus : star ((ρ g : unitary (E →L[ℂ] E)) : E →L[ℂ] E)
      * ((ρ g : unitary (E →L[ℂ] E)) : E →L[ℂ] E) = 1 := (ρ g).2.1
  calc ((ρ g : unitary (E →L[ℂ] E)) : E →L[ℂ] E)
        * CStarSpectralProjection.spectralProjection (unitaryAverage ρ S) c
      = ((ρ g : unitary (E →L[ℂ] E)) : E →L[ℂ] E)
          * CStarSpectralProjection.spectralProjection (unitaryAverage ρ S) c
          * (star ((ρ g : unitary (E →L[ℂ] E)) : E →L[ℂ] E)
            * ((ρ g : unitary (E →L[ℂ] E)) : E →L[ℂ] E)) := by
        rw [hus, mul_one]
    _ = (((ρ g : unitary (E →L[ℂ] E)) : E →L[ℂ] E)
          * CStarSpectralProjection.spectralProjection (unitaryAverage ρ S) c
          * star ((ρ g : unitary (E →L[ℂ] E)) : E →L[ℂ] E))
          * ((ρ g : unitary (E →L[ℂ] E)) : E →L[ℂ] E) := by noncomm_ring
    _ = CStarSpectralProjection.spectralProjection (unitaryAverage ρ S) c
          * ((ρ g : unitary (E →L[ℂ] E)) : E →L[ℂ] E) := by rw [hconj]

/-- **`q = 1 − P` commutes with `π(g)`.**  The printed "so `P` and `q` commute
with `π(H̄)` exactly". -/
theorem commute_one_sub_spectralProjection {S : Finset G} (hS : S.Nonempty)
    (hsymm : ∀ g ∈ S, g⁻¹ ∈ S) {c : ℝ} (hc : c < 1)
    (hgap : ∀ μ ∈ spectrum ℝ (unitaryAverage ρ S), μ ≤ c ∨ μ = 1)
    (hnorm : ∀ g : G, ∀ k ∈ Subgroup.closure (S : Set G),
      g * k * g⁻¹ ∈ Subgroup.closure (S : Set G))
    (g : G) :
    ((ρ g : unitary (E →L[ℂ] E)) : E →L[ℂ] E)
        * ((1 : E →L[ℂ] E)
          - CStarSpectralProjection.spectralProjection (unitaryAverage ρ S) c)
      = ((1 : E →L[ℂ] E)
          - CStarSpectralProjection.spectralProjection (unitaryAverage ρ S) c)
        * ((ρ g : unitary (E →L[ℂ] E)) : E →L[ℂ] E) := by
  rw [mul_sub, sub_mul, one_mul, mul_one,
    commute_spectralProjection ρ hS hsymm hc hgap hnorm g]

end Normality

end

end UnitaryAverageFixedVector
end GroupApproximation
