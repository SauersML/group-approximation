import GroupApproximation.Analysis.CollapseProjectionLift
import GroupApproximation.Analysis.RankNormalizedLambda

/-!
# The printed discarding step, as a choice of ultrafilter

Proof-ledger row `CO.20`.  The row's Claim ends with the printed sentence

> since `q ≠ 0`, `Q_n ≠ 0` for infinitely many `n`; discard the remaining
> coordinates, relabel by `ℕ`, and put `k_n = rank Q_n ≥ 1`,

and the row records this as the one clause still carried as a hypothesis:
`norm_lambda_projection` asks for `∀ n, 0 < rank Q_n`, which the printed proof
arranges by discarding coordinates.  The note there also states the honest
alternative, and this file takes it.

Discarding coordinates changes the index set and therefore the ultrafilter,
which is what made the printed sentence awkward to formalize literally.  But
the ultrafilter is not given in advance — the printed proof is free to choose
it, and choosing it *containing* the set where `Q_n ≠ 0` does exactly what
discarding does, without reindexing anything:

* `norm_mkK_projection_eventually` weakens `‖Λ(q)‖ = 1` to need positivity of
  the rank only on a set of `ω`, which is all the ultralimit sees;
* `exists_free_ultrafilter_rank_pos` produces such an `ω`, free, from `q ≠ 0`
  alone — the set where the projection lift is nonzero is infinite, hence
  meets every cofinite set, so `cofinite ⊓ 𝓟 S` is proper and any ultrafilter
  refining it is free and contains `S`.

So the clause is discharged rather than assumed, and no relabelling occurs.

`rank_pos_of_ne_zero` is the arithmetic the sentence leaves implicit: a
projection of rank zero has zero Frobenius mass, hence is zero.
-/

namespace GroupApproximation
namespace CollapseDiscardCoordinates

open Filter Matrix Topology
open UltrafilterLimit UltraproductModelConstruction ScaledKazhdanTransport
open KazhdanCornerMatrices
open RankNormalizedHilbertization RankNormalizedLambda KOmegaHilbert
open scoped Matrix.Norms.L2Operator

noncomputable section

/-! ## A nonzero projection has positive rank -/

/-- A projection of rank zero is zero: its Frobenius mass is its rank. -/
theorem eq_zero_of_rank_eq_zero {Z : Type*} [Fintype Z] [DecidableEq Z]
    {P : Matrix Z Z ℂ} (hP : IsOrthogonalProjectionMatrix P)
    (h : P.rank = 0) : P = 0 := by
  refine UltraproductScaledTransport.eq_zero_of_matMass_eq_zero ?_
  rw [matMass_eq_rank_of_isOrthogonalProjection hP, h]
  norm_num

/-- The printed `k_n = rank Q_n ≥ 1`, at a coordinate where `Q_n ≠ 0`. -/
theorem rank_pos_of_ne_zero {Z : Type*} [Fintype Z] [DecidableEq Z]
    {P : Matrix Z Z ℂ} (hP : IsOrthogonalProjectionMatrix P) (h : P ≠ 0) :
    0 < P.rank := by
  rcases Nat.eq_zero_or_pos P.rank with h0 | hpos
  · exact absurd (eq_zero_of_rank_eq_zero hP h0) h
  · exact hpos

/-! ## `‖Λ(q)‖ = 1` needs the rank only on a set of `ω` -/

variable (Y : ℕ → FiniteModel)

/-- **`‖Λ(q)‖ = 1`, with the rank positive only `ω`-eventually.**  The norm of
a class is an ultralimit, and an ultralimit sees a family only on sets of `ω`,
so the printed `k_n ≥ 1` is needed exactly there and not at every
coordinate. -/
theorem norm_mkK_projection_eventually (ω : Ultrafilter ℕ) (P : MatFam Y)
    (hP : ∀ n, IsOrthogonalProjectionMatrix (P n))
    (hrk : ∀ᶠ n in (ω : Filter ℕ), 0 < (P n).rank)
    (ξ : massBounded Y (rankWeight Y P)) (hξ : (ξ : MatFam Y) = P) :
    ‖mkK Y (rankWeight Y P) ω (rankWeight_nonneg Y P) ξ‖ = 1 := by
  rw [norm_mkK]
  have hcong : ∀ᶠ n in (ω : Filter ℕ),
      matMass ((ξ : MatFam Y) n) / rankWeight Y P n = (1 : ℝ) := by
    filter_upwards [hrk] with n hn
    rw [hξ]
    show matMass (P n) / ((P n).rank : ℝ) = 1
    rw [matMass_eq_rank_of_isOrthogonalProjection (hP n)]
    exact div_self (Nat.cast_ne_zero.mpr hn.ne')
  rw [ulim_congr hcong
    (HilbertUltraproductInner.exists_tendsto_mass (rankWeight_nonneg Y P) ξ),
    ulim_const, Real.sqrt_one]

/-! ## The choice of ultrafilter -/

variable [∀ n, Nonempty (Y n)]

/-- **The printed discarding step.**  If the projection lift is nonzero in the
corona then there is a *free* ultrafilter along which its rank is
`ω`-eventually positive.

This is what "discard the remaining coordinates and relabel" accomplishes, and
it accomplishes it without reindexing: `q ≠ 0` says the lift is nonzero at
infinitely many coordinates, an infinite set meets every cofinite set, so
`cofinite ⊓ 𝓟 S` is a proper filter and any ultrafilter refining it is free
and contains `S`.  The printed proof is free to choose `ω`, and this is the
choice it is making. -/
theorem exists_free_ultrafilter_rank_pos
    (Q : BoundedMatrixSequence (fun n ↦ Y n))
    (hQ : ∀ n, IsOrthogonalProjectionMatrix (Q n))
    (hne : normMatrixCStarCoronaMk (fun n ↦ Y n) Q ≠ 0) :
    ∃ ω : Ultrafilter ℕ, (ω : Filter ℕ) ≤ cofinite ∧
      ∀ᶠ n in (ω : Filter ℕ), 0 < (Q n).rank := by
  classical
  have hinf : {n : ℕ | (Q n : Matrix (Y n) (Y n) ℂ) ≠ 0}.Infinite := by
    intro hfin
    refine hne ((normMatrixCStarCoronaMk_eq_zero_iff (fun n ↦ Y n) Q).mpr ?_)
    show Tendsto (fun n ↦ ‖(Q n : Matrix (Y n) (Y n) ℂ)‖) cofinite (nhds 0)
    have hev : ∀ᶠ n in cofinite, ‖(Q n : Matrix (Y n) (Y n) ℂ)‖ = 0 := by
      rw [Filter.eventually_cofinite]
      refine Set.Finite.subset hfin ?_
      intro n hn
      simp only [Set.mem_setOf_eq] at hn ⊢
      intro hz
      exact hn (by rw [hz, norm_zero])
    exact Tendsto.congr' (hev.mono fun n hn ↦ hn.symm) tendsto_const_nhds
  haveI hnb : (cofinite ⊓ 𝓟 {n : ℕ | (Q n : Matrix (Y n) (Y n) ℂ) ≠ 0} :
      Filter ℕ).NeBot := by
    rw [Filter.inf_principal_neBot_iff]
    intro U hU
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    refine hinf (Set.Finite.subset (Filter.mem_cofinite.mp hU) ?_)
    intro n hn
    by_contra hn'
    have hnU : n ∈ U := by
      by_contra hc
      exact hn' hc
    have hmem : n ∈ U ∩ {n : ℕ | (Q n : Matrix (Y n) (Y n) ℂ) ≠ 0} :=
      ⟨hnU, hn⟩
    rw [hempty] at hmem
    exact hmem
  refine ⟨Ultrafilter.of
    (cofinite ⊓ 𝓟 {n : ℕ | (Q n : Matrix (Y n) (Y n) ℂ) ≠ 0}), ?_, ?_⟩
  · exact le_trans (Ultrafilter.of_le _) inf_le_left
  · have hmem : {n : ℕ | (Q n : Matrix (Y n) (Y n) ℂ) ≠ 0}
        ∈ (Ultrafilter.of
          (cofinite ⊓ 𝓟 {n : ℕ | (Q n : Matrix (Y n) (Y n) ℂ) ≠ 0}) :
          Filter ℕ) :=
      Ultrafilter.of_le _ (Filter.mem_inf_of_right (Filter.mem_principal_self _))
    filter_upwards [hmem] with n hn
    exact rank_pos_of_ne_zero (hQ n) hn

end

end CollapseDiscardCoordinates
end GroupApproximation
