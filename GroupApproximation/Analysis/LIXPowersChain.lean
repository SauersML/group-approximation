import GroupApproximation.Analysis.LIXPowersHomotopy

/-!
# The powers chain, assembled

`notes/LIX_STRONGER_PROGRAM_2026-09-10.md` §1.3 items 1--3, in one statement.  This file
composes the four pieces the lane built:

1. `clutchEquiv_normGen_pow` — the generator's `m`-th power and its renormalisation's clutch
   equivalent projections (a gauge step, no homotopy);
2. `exists_partialIsometry_pow_reparProd` — Eckmann--Hilton, `ũ^{k+1}` against the ordered
   product of the `k+1` angle reparametrisations;
3. `pinchIdentification_angleRepar` — the ordered product collapses to `ũ ∘ ψ_k`, using
   `normGen_wall`;
4. `clutchEquiv_normGen_comp` — back from `ũ ∘ ψ_k` to `u ∘ ψ_k` (a gauge step again).

**This file is the geometric statement, and it is NOT on the critical path** (lead,
2026-09-10).  The C*-side chain never clutches: it glues the two hemisphere frames of
`LIXGeneratorUnitary` into a unitary field, and what it consumes is the *homotopy of maps*
of `Analysis/LIXPowersHomotopy.lean`, not an equivalence of projections.  Keep this file for
what it says about the geometry; do not route the endpoint through it.

The result, `clutchEquiv_pow_pullback`, is, in the `Analysis/` vocabulary:

```text
clutch (u^{k+1})  ≅  clutch u  read at  Σψ_k
```

with `≅` the Murray--von Neumann equivalence of continuous projection fields
(`Powers.ClutchEquiv`, which is the same shape as `CharClass.ContinuousMvNEquiv`).

## What the caller has to supply

Only that the generator is a **ball unitary** — continuous on `E`, unitary on the closed
unit ball — and that `e₁, e₂` are orthonormal.  In particular there is **no basepoint
condition on the generator**: the renormalisation is internal to the chain, and it is a
gauge step rather than a contraction, so nothing about the topology of `U(n)` is used.  See
`Analysis/LIXPowersNormalise.lean` for why.

## The one thing this file does not do

It does not identify `clutch u` with `Fproj = 1 − x xᴴ`, nor `clutch (u ∘ ψ_k)` with
`(x ∘ Σψ_k)^⊥ ⊕ H`.  That identification lives in `CharClass` vocabulary
(`CharClass.FHmat`/`EHmat` over `VIdx dd = Fin 3 ⊕ HIdx dd`) and is `Fin 3`-bound until the
rank generalisation of `VIdx`/`baseM` lands; it is a bridge of one `Iff.rfl` plus that
identification, and it belongs with the lane that owns those files.
-/

namespace GroupApproximation
namespace LIX
namespace Powers

open scoped Matrix

set_option linter.unusedSectionVars false

noncomputable section

section Chain

variable {X : Type*} [TopologicalSpace X] {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] {e₁ e₂ : E} {n : Type*} [Fintype n] [DecidableEq n]
  {t : X → ℝ} {ν : X → E} {U : E → Matrix n n ℂ}

theorem norm_equator_mul (hc : IsSuspensionChart t ν) (x : X) :
    ‖ν x‖ * ‖ν x‖ = 1 - t x ^ 2 := by
  nlinarith [hc.sphere x]

/-- The cone of a ball unitary is a clutching datum at every point of the chart. -/
theorem isClutchDatum_coneMat_of_ballUnitary (hc : IsSuspensionChart t ν)
    {W : E → Matrix n n ℂ} (hW : IsBallUnitary W) (x : X) :
    IsClutchDatum (t x) (coneMat W (ν x)) := by
  rw [coneMat_apply_equator]
  exact isClutchDatum_smul (norm_equator_mul hc x)
    (hW.star_mul_self _ (norm_chartDir_le_one ν x))
    (hW.mul_star_self _ (norm_chartDir_le_one ν x))

/-- Hence the clutched projection really is idempotent, which is what `ClutchEquiv.trans`
asks of its two outer arguments. -/
theorem clutchMat_idem (hc : IsSuspensionChart t ν) {W : E → Matrix n n ℂ}
    (hW : IsBallUnitary W) (x : X) :
    clutchMat (t x) (coneMat W (ν x)) * clutchMat (t x) (coneMat W (ν x))
      = clutchMat (t x) (coneMat W (ν x)) :=
  clutchMat_mul_self (isClutchDatum_coneMat_of_ballUnitary hc hW x)

/-- **The powers chain.**  The projection clutched by the `(k+1)`-st pointwise power of a
seam generator is Murray--von Neumann equivalent, through an explicit continuous partial
isometry, to the projection clutched by the generator itself *read at* `Σψ_k`.

No hypothesis on the generator beyond unitarity on the closed ball. -/
theorem clutchEquiv_pow_pullback (hc : IsSuspensionChart t ν) (h₁ : ‖e₁‖ = 1)
    (h₂ : ‖e₂‖ = 1) (h₁₂ : inner ℝ e₁ e₂ = (0 : ℝ)) (hU : IsBallUnitary U) (k : ℕ) :
    ClutchEquiv
      (fun x => clutchMat (t x) (coneMat (fun y => (U y) ^ (k + 1)) (ν x)))
      (fun x => clutchMat (t x) (coneMat U (joinPowNeg e₁ e₂ k (ν x)))) := by
  have hΨ : IsRadialMap (joinPowNeg e₁ e₂ k) := isRadialMap_joinPowNeg h₁ h₂ h₁₂ k
  have hnorm : IsBallUnitary (normGen e₁ e₂ U) := isBallUnitary_normGen h₁ h₂ h₁₂ hU
  have hcΨ : IsSuspensionChart t fun x => joinPowNeg e₁ e₂ k (ν x) :=
    isSuspensionChart_comp_radial hc hΨ
  -- (1) the powers, before and after renormalisation
  have E1 := clutchEquiv_normGen_pow hc h₁ h₂ h₁₂ hU (k + 1)
  -- (2)+(3) Eckmann--Hilton and the pinch identification, for the renormalised generator
  obtain ⟨V, hVc, hV1, hV2⟩ :=
    exists_partialIsometry_pow_pullback (W := normGen e₁ e₂ U) (P := angleFam e₁ e₂ k)
      (Ψ := joinPowNeg e₁ e₂ k) hc hnorm (continuous_angleFam e₁ e₂ k)
      (angleFam_param_zero e₁ e₂ k)
      (fun j θ y hy => le_of_eq_of_le (norm_angleFam h₁ h₂ h₁₂ k j θ y) hy) hΨ
      (pinchIdentification_angleRepar h₁ h₂ h₁₂ k
        (fun y hy => normGen_wall h₁ h₂ h₁₂ hU hy))
  have E2 : ClutchEquiv
      (fun x => clutchMat (t x) (coneMat (normGen e₁ e₂ U) (joinPowNeg e₁ e₂ k (ν x))))
      (fun x => clutchMat (t x)
        (coneMat (fun y => (normGen e₁ e₂ U y) ^ (k + 1)) (ν x))) :=
    ⟨V, hVc, hV1, hV2⟩
  -- (4) back from the renormalised generator, along `ψ_k`
  have E3raw := clutchEquiv_normGen_comp hc h₁ h₂ h₁₂ hU hΨ
  have E3 : ClutchEquiv
      (fun x => clutchMat (t x) (coneMat U (joinPowNeg e₁ e₂ k (ν x))))
      (fun x => clutchMat (t x)
        (coneMat (normGen e₁ e₂ U) (joinPowNeg e₁ e₂ k (ν x)))) := by
    have hrw : ∀ (W : E → Matrix n n ℂ) (x : X),
        coneMat W (joinPowNeg e₁ e₂ k (ν x))
          = coneMat (fun y => W (joinPowNeg e₁ e₂ k y)) (ν x) :=
      fun W x => coneMat_comp_radial hΨ W (ν x)
    simpa only [hrw] using E3raw
  -- the idempotence side conditions
  have hidA : ∀ x : X, clutchMat (t x) (coneMat (fun y => (U y) ^ (k + 1)) (ν x)) *
      clutchMat (t x) (coneMat (fun y => (U y) ^ (k + 1)) (ν x))
      = clutchMat (t x) (coneMat (fun y => (U y) ^ (k + 1)) (ν x)) :=
    clutchMat_idem hc (hU.pow (k + 1))
  have hidC : ∀ x : X, clutchMat (t x) (coneMat U (joinPowNeg e₁ e₂ k (ν x))) *
      clutchMat (t x) (coneMat U (joinPowNeg e₁ e₂ k (ν x)))
      = clutchMat (t x) (coneMat U (joinPowNeg e₁ e₂ k (ν x))) :=
    clutchMat_idem hcΨ hU
  have hidC' : ∀ x : X,
      clutchMat (t x) (coneMat (normGen e₁ e₂ U) (joinPowNeg e₁ e₂ k (ν x))) *
        clutchMat (t x) (coneMat (normGen e₁ e₂ U) (joinPowNeg e₁ e₂ k (ν x)))
      = clutchMat (t x) (coneMat (normGen e₁ e₂ U) (joinPowNeg e₁ e₂ k (ν x))) :=
    clutchMat_idem hcΨ hnorm
  exact ClutchEquiv.trans hidA hidC (ClutchEquiv.trans hidA hidC' E1 E2.symm) E3.symm

/-- The same statement with the composite written out, which is the form
`Analysis/LIXPowersNaturality.lean` phrases naturality in. -/
theorem clutchEquiv_pow_comp (hc : IsSuspensionChart t ν) (h₁ : ‖e₁‖ = 1) (h₂ : ‖e₂‖ = 1)
    (h₁₂ : inner ℝ e₁ e₂ = (0 : ℝ)) (hU : IsBallUnitary U) (k : ℕ) :
    ClutchEquiv
      (fun x => clutchMat (t x) (coneMat (fun y => (U y) ^ (k + 1)) (ν x)))
      (fun x => clutchMat (t x)
        (coneMat (fun y => U (joinPowNeg e₁ e₂ k y)) (ν x))) := by
  have hΨ : IsRadialMap (joinPowNeg e₁ e₂ k) := isRadialMap_joinPowNeg h₁ h₂ h₁₂ k
  have hrw : ∀ x : X, coneMat U (joinPowNeg e₁ e₂ k (ν x))
      = coneMat (fun y => U (joinPowNeg e₁ e₂ k y)) (ν x) :=
    fun x => coneMat_comp_radial hΨ U (ν x)
  simpa only [hrw] using clutchEquiv_pow_pullback hc h₁ h₂ h₁₂ hU k

/-- **The transported form.**  If the suspension `Σψ_k` is realised as an honest self-map
`Φ` of the parameter space -- fixing the height and moving the equatorial part by `ψ_k` --
then the projection clutched by `u^{k+1}` at `x` is equivalent to the projection clutched
by `u` at `Φ x`.  This is the shape Step C reads its section data in. -/
theorem clutchEquiv_pow_pullback_map (hc : IsSuspensionChart t ν) (h₁ : ‖e₁‖ = 1)
    (h₂ : ‖e₂‖ = 1) (h₁₂ : inner ℝ e₁ e₂ = (0 : ℝ)) (hU : IsBallUnitary U) (k : ℕ)
    {Φ : X → X} (hΦt : ∀ x, t (Φ x) = t x)
    (hΦν : ∀ x, ν (Φ x) = joinPowNeg e₁ e₂ k (ν x)) :
    ClutchEquiv
      (fun x => clutchMat (t x) (coneMat (fun y => (U y) ^ (k + 1)) (ν x)))
      (fun x => clutchMat (t (Φ x)) (coneMat U (ν (Φ x)))) := by
  have hrw : ∀ x : X, clutchMat (t (Φ x)) (coneMat U (ν (Φ x)))
      = clutchMat (t x) (coneMat U (joinPowNeg e₁ e₂ k (ν x))) := by
    intro x
    rw [hΦt, hΦν]
  simpa only [hrw] using clutchEquiv_pow_pullback hc h₁ h₂ h₁₂ hU k

/-- **The hand-off to Step C.**  If the projection clutched by the generator is identified
with a given field `P` -- which is what Lemma 6 supplies, `clutch u = Fproj ⊕ H` -- then the
projection clutched by `u^{k+1}` is Murray--von Neumann equivalent to `P` read at `Σψ_k`.

This is the statement `sp-oddside` consumes.  Instantiating it in `CharClass` vocabulary is
mechanical: `Powers.ClutchEquiv` and `CharClass.ContinuousMvNEquiv` are the *same*
definition unfolded, so the bridge between them is `Iff.rfl`, and `P` is `FHmat` with the
transported section.  That instantiation is not done here, because it would put a
`CharClass` import under the clutching layer for the sake of one `Iff.rfl`; it belongs in
the file that already imports `CharClass`. -/
theorem clutchEquiv_pow_of_clutch_eq (hc : IsSuspensionChart t ν) (h₁ : ‖e₁‖ = 1)
    (h₂ : ‖e₂‖ = 1) (h₁₂ : inner ℝ e₁ e₂ = (0 : ℝ)) (hU : IsBallUnitary U) (k : ℕ)
    {Φ : X → X} (hΦt : ∀ x, t (Φ x) = t x)
    (hΦν : ∀ x, ν (Φ x) = joinPowNeg e₁ e₂ k (ν x))
    {P : X → Matrix (n ⊕ n) (n ⊕ n) ℂ}
    (hP : ∀ x, clutchMat (t x) (coneMat U (ν x)) = P x) :
    ClutchEquiv
      (fun x => clutchMat (t x) (coneMat (fun y => (U y) ^ (k + 1)) (ν x)))
      (fun x => P (Φ x)) := by
  simpa only [hP] using clutchEquiv_pow_pullback_map hc h₁ h₂ h₁₂ hU k hΦt hΦν

end Chain

end

end Powers
end LIX
end GroupApproximation
