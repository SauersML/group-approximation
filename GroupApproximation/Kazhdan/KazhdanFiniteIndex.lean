import GroupApproximation.Kazhdan.InducedRepresentation
import GroupApproximation.Kazhdan.SharpExistenceRoutes

/-!
# Property `(T)` passes to finite-index subgroups

This module proves the theorem `Kazhdan/SharpExistenceRoutes.lean` records as
`Hyperbolic.KazhdanFiniteIndexPermanence` and does not prove:

> if `Λ ≤ Γ` has finite index and `Γ` has Kazhdan's property `(T)`, then so
> does `Λ`.

This is Bekka--de la Harpe--Valette, *Kazhdan's Property (T)*, Theorem 1.7.1
(there stated for a lattice in a locally compact group; a finite-index subgroup
of a discrete group is the discrete case).  `hasKazhdanPropertyT_of_finiteIndex`
is the theorem, `kazhdanFiniteIndexPermanence` is the packaged statement, and
`sharpExistence_of_latticeRoute'` is the consequence for the lattice route to
`Hyperbolic.SharpExistence`: **one of its three permanence inputs is now
discharged**, and only hyperbolicity (an instance of the Morse lemma) and finite
presentation (Reidemeister--Schreier) remain.

## The proof

Induction of representations, made completely explicit by
`Kazhdan/InducedRepresentation.lean`.  Given a Kazhdan pair `(Q, ε)` for `Γ`,
the pair produced for `Λ` is

* the *same* tolerance `ε` --- induction of the constant vector loses nothing,
  because the displacement of the constant vector is the root mean square of the
  displacements of `v` by the cocycle values, and a mean of numbers below `ε`
  is below `ε`;
* the finite set of cocycle values `Q_Λ = { c·q·sec(c·q)⁻¹ : c ∈ reps, q ∈ Q }`,
  which is finite exactly because the index is finite.

Given an orthogonal representation `π` of `Λ` with a `(Q_Λ, ε)`-almost invariant
unit vector `v`, the constant vector of `Ind π` is `(Q, ε)`-almost invariant
after normalisation, so property `(T)` for `Γ` produces a nonzero invariant
vector of `Ind π`, whose coordinate at the base index is a nonzero `π`-invariant
vector.  No completion, no direct-integral decomposition and no continuity
argument is needed: the induced space is a *finite* direct sum, which is what
finiteness of the index buys.

## Universes

Stated as `HasKazhdanPropertyT.{u, max u v} Γ → HasKazhdanPropertyT.{u, v} ↥Λ`.
The induced space of a representation on `E : Type v` is indexed by the coset
representatives, which live in `Type u`, so it lands in `Type (max u v)`: the
hypothesis is used at exactly the universe the construction produces, and no
universe-independence theorem for `HasKazhdanPropertyT` is assumed.  At `u = v =
0` --- the shape `Hyperbolic.KazhdanFiniteIndexPermanence` asks for --- the two
universes coincide.
-/

namespace GroupApproximation
namespace FiniteIndex

universe u v

/-- **Property `(T)` passes to a finite-index subgroup**
(Bekka--de la Harpe--Valette, Theorem 1.7.1).

The Kazhdan set produced for `Λ` is the finite set of values of the transversal
cocycle on `reps × Q`, and the tolerance is unchanged. -/
theorem hasKazhdanPropertyT_of_finiteIndex {Γ : Type u} [Group Γ] (Λ : Subgroup Γ)
    [Λ.FiniteIndex] (hΓ : HasKazhdanPropertyT.{u, max u v} Γ) :
    HasKazhdanPropertyT.{u, v} ↥Λ := by
  classical
  obtain ⟨Q, ε, hε, hQ⟩ := hΓ
  obtain ⟨tr⟩ := exists_rightTransversal Λ
  haveI : Nonempty (Index tr) := ⟨baseIndex tr⟩
  refine ⟨(tr.reps ×ˢ Q).image (fun p : Γ × Γ => cocycle tr p.1 p.2), ε, hε, ?_⟩
  intro E _ _ _ π v hv hnear
  -- The constant vector, and its norm.
  set ξ₀ : IndSpace tr E := constVec tr E v with hξ₀def
  have hcard : (0 : ℝ) < (Fintype.card (Index tr) : ℝ) := by
    exact_mod_cast Fintype.card_pos (α := Index tr)
  have hξ₀sq : ‖ξ₀‖ ^ 2 = (Fintype.card (Index tr) : ℝ) := by
    rw [hξ₀def, norm_constVec_sq, hv]
    ring
  have hξ₀pos : 0 < ‖ξ₀‖ := by
    nlinarith [norm_nonneg ξ₀, hξ₀sq, hcard]
  have hξnorm : ‖(‖ξ₀‖⁻¹ : ℝ) • ξ₀‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hξ₀pos),
      inv_mul_cancel₀ hξ₀pos.ne']
  -- Every cocycle value in a direction from `Q` lies in the Kazhdan set of `Λ`.
  have hcoord : ∀ q ∈ Q, ∀ c : Index tr, ‖π (cocycle tr c.1 q) v - v‖ < ε := by
    intro q hq c
    refine hnear _ ?_
    refine Finset.mem_image.mpr ⟨(c.1, q), ?_, rfl⟩
    exact Finset.mem_product.mpr ⟨c.2, hq⟩
  -- The normalised constant vector is almost invariant for the induced representation.
  have hclose : ∀ q ∈ Q,
      ‖ind tr E π q ((‖ξ₀‖⁻¹ : ℝ) • ξ₀) - (‖ξ₀‖⁻¹ : ℝ) • ξ₀‖ < ε := by
    intro q hq
    have hsum : ‖indFun tr E π q ξ₀ - ξ₀‖ ^ 2 < ‖ξ₀‖ ^ 2 * ε ^ 2 := by
      rw [hξ₀sq, hξ₀def, norm_indFun_constVec_sub_sq]
      calc ∑ c : Index tr, ‖π (cocycle tr c.1 q) v - v‖ ^ 2
          < ∑ _c : Index tr, ε ^ 2 := by
            refine Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun c _ => ?_
            nlinarith [norm_nonneg (π (cocycle tr c.1 q) v - v), hcoord q hq c]
        _ = (Fintype.card (Index tr) : ℝ) * ε ^ 2 := by
            simp [nsmul_eq_mul]
    have hstep : ‖indFun tr E π q ξ₀ - ξ₀‖ < ‖ξ₀‖ * ε := by
      nlinarith [norm_nonneg (indFun tr E π q ξ₀ - ξ₀), hsum, mul_pos hξ₀pos hε]
    have hlin : ind tr E π q ((‖ξ₀‖⁻¹ : ℝ) • ξ₀) - (‖ξ₀‖⁻¹ : ℝ) • ξ₀
        = (‖ξ₀‖⁻¹ : ℝ) • (indFun tr E π q ξ₀ - ξ₀) := by
      rw [ind_apply, indFun_smul, smul_sub]
    rw [hlin, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hξ₀pos)]
    have hmul := mul_lt_mul_of_pos_left hstep (inv_pos.mpr hξ₀pos)
    rwa [← mul_assoc, inv_mul_cancel₀ hξ₀pos.ne', one_mul] at hmul
  -- Property `(T)` for `Γ` produces an invariant vector upstairs, ...
  obtain ⟨y, hy0, hyinv⟩ :=
    hQ (IndSpace tr E) (ind tr E π) ((‖ξ₀‖⁻¹ : ℝ) • ξ₀) hξnorm hclose
  -- ... and its base coordinate is an invariant vector downstairs.
  exact exists_invariant_of_invariant tr E π y hy0 hyinv

/-- **The packaged statement**: `Hyperbolic.KazhdanFiniteIndexPermanence`, which
`Kazhdan/SharpExistenceRoutes.lean` states and leaves open, is a theorem. -/
theorem kazhdanFiniteIndexPermanence : Hyperbolic.KazhdanFiniteIndexPermanence := by
  intro Γ inst Λ hfi hΓ
  exact @hasKazhdanPropertyT_of_finiteIndex Γ inst Λ hfi hΓ

/-- **The lattice route, with the Kazhdan input discharged.**  Compare
`Hyperbolic.sharpExistence_of_latticeRoute`, which needs three permanence
properties: property `(T)` no longer has to be assumed, so the distance from
this repository to `Hyperbolic.SharpExistence` is now hyperbolicity (the Morse
lemma) plus finite presentation (Reidemeister--Schreier) plus the lattice
itself. -/
theorem sharpExistence_of_latticeRoute'
    (h₁ : Hyperbolic.HyperbolicFiniteIndexPermanence)
    (h₃ : Hyperbolic.FinitePresentationFiniteIndexPermanence)
    (L : Hyperbolic.LatticeRouteInput) : Hyperbolic.SharpExistence :=
  Hyperbolic.sharpExistence_of_latticeRoute h₁ kazhdanFiniteIndexPermanence h₃ L

end FiniteIndex
end GroupApproximation
