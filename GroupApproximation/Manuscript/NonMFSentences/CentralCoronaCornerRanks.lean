import GroupApproximation.Manuscript.OneSidedMFRadical.CentralCoronaCornerPrintedRoute
import GroupApproximation.Meta.AxiomGuard

/-!
# `lem:central-corona-corner`: retaining the coordinates and `r_n = rank(q_n)`

`non_mf_groups_exist.tex`, proof of Lemma `lem:central-corona-corner` (tex lines
630-632 at 73c867c5b):

> Lift `q` to projections `q_n ∈ M_{d_n}(ℂ)` by functional calculus.  Since
> `q ≠ 0`, infinitely many `q_n` are nonzero; retain those coordinates and put
> `r_n = rank(q_n)`.

`Manuscript/OneSidedMFRadical/CentralCoronaCornerPrintedRoute.lean` proves the
first half of the second sentence (`manuscriptSentence_retainedCoordinatesInfinite`)
and records in its header that `r_n = rank(q_n)` is *not* claimed there: the
corner models are indexed by the eigen-coordinates of `q_n` above `1/2`, and only
their positivity is proved.  This module supplies the rest of the sentence:

* the retained coordinates are enumerated by `Nat.nth` of the predicate
  `q_n ≠ 0`, a strictly increasing map whose range is exactly the set of
  nonzero coordinates ("retain those coordinates");
* at every retained coordinate the corner model has exactly `rank(q_n)` points,
  and `rank(q_n) ≥ 1` ("put `r_n = rank(q_n)`", with the lemma's `r_n ≥ 1`).

The rank identity is spectral: a Hermitian idempotent has eigenvalues `0` and
`1` only (`PrintedCornerCompression.eigenvalues_eq_zero_or_one`), so the corner
coordinates (eigenvalue above `1/2`) are exactly the coordinates of nonzero
eigenvalue, whose number is the rank (`Matrix.IsHermitian.rank_eq_card_non_zero_eigs`).
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMFSentences

open Filter Matrix
open OneSidedMFRadical
open PrintedCornerCompression KazhdanCornerMatrices

noncomputable section

/-- **A Hermitian idempotent: the corner coordinates are counted by the rank.**
The coordinates of the eigenbasis of `q` above `1/2` (the printed corner
`q ℂ^d ≅ ℂ^r`) number exactly `rank q`. -/
theorem card_cornerPredicate_eq_rank {Y : Type*} [Fintype Y] [DecidableEq Y]
    {q : Matrix Y Y ℂ} (hq : q.IsHermitian) (hidem : q * q = q) :
    Fintype.card {i : Y // cornerPredicate hq i} = q.rank := by
  rw [hq.rank_eq_card_non_zero_eigs]
  refine Fintype.card_congr (Equiv.subtypeEquivRight fun i ↦ ?_)
  change (1 / 2 : ℝ) < hq.eigenvalues i ↔ hq.eigenvalues i ≠ 0
  rcases eigenvalues_eq_zero_or_one hq hidem i with h0 | h1
  · rw [h0]
    norm_num
  · rw [h1]
    norm_num

/-- **A nonzero Hermitian idempotent has rank at least one.** -/
theorem one_le_rank_of_ne_zero {Y : Type*} [Fintype Y] [DecidableEq Y]
    {q : Matrix Y Y ℂ} (hq : q.IsHermitian) (hidem : q * q = q) (hne : q ≠ 0) :
    1 ≤ q.rank := by
  rw [← card_cornerPredicate_eq_rank hq hidem]
  obtain ⟨i, hi⟩ := cornerPredicate_exists hq hidem hne
  exact Fintype.card_pos_iff.mpr ⟨⟨i, hi⟩⟩

/-- **`lem:central-corona-corner`, proof sentence (tex lines 630-632), every
clause.**  For a projection lift `(q_n)` of a nonzero projection `q` of the norm
matrix corona `𝒬_d`:

1. infinitely many `q_n` are nonzero;
2. retaining those coordinates is the strictly increasing enumeration
   `Nat.nth (q_n ≠ 0)`, whose range is exactly `{n | q_n ≠ 0}`;
3. at the `k`-th retained coordinate `n`, the corner `q_n M_{d_n}(ℂ) q_n` is
   indexed by exactly `r_n = rank(q_n)` coordinates, and `r_n ≥ 1`. -/
def PrintedRetainedCoordinatesAndRanks : Prop :=
  ∀ (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]
    (Q : BoundedMatrixSequence (fun n ↦ X n))
    (q : NormMatrixCStarCorona (fun n ↦ X n))
    (hQ : ∀ n, IsOrthogonalProjectionMatrix ((Q : ∀ n, Matrix (X n) (X n) ℂ) n)),
    normMatrixCStarCoronaMk (fun n ↦ X n) Q = q → q ≠ 0 →
      {n : ℕ | (Q : ∀ n, Matrix (X n) (X n) ℂ) n ≠ 0}.Infinite ∧
      StrictMono (Nat.nth fun n ↦ (Q : ∀ n, Matrix (X n) (X n) ℂ) n ≠ 0) ∧
      Set.range (Nat.nth fun n ↦ (Q : ∀ n, Matrix (X n) (X n) ℂ) n ≠ 0)
        = {n : ℕ | (Q : ∀ n, Matrix (X n) (X n) ℂ) n ≠ 0} ∧
      ∀ k : ℕ,
        (Q : ∀ n, Matrix (X n) (X n) ℂ)
            (Nat.nth (fun n ↦ (Q : ∀ n, Matrix (X n) (X n) ℂ) n ≠ 0) k) ≠ 0 ∧
        1 ≤ ((Q : ∀ n, Matrix (X n) (X n) ℂ)
            (Nat.nth (fun n ↦ (Q : ∀ n, Matrix (X n) (X n) ℂ) n ≠ 0) k)).rank ∧
        Fintype.card {i : X (Nat.nth (fun n ↦ (Q : ∀ n, Matrix (X n) (X n) ℂ) n ≠ 0) k) //
            cornerPredicate
              ((hQ (Nat.nth (fun n ↦ (Q : ∀ n, Matrix (X n) (X n) ℂ) n ≠ 0) k)).1 :
                ((Q : ∀ n, Matrix (X n) (X n) ℂ)
                  (Nat.nth (fun n ↦ (Q : ∀ n, Matrix (X n) (X n) ℂ) n ≠ 0) k)).IsHermitian)
              i}
          = ((Q : ∀ n, Matrix (X n) (X n) ℂ)
              (Nat.nth (fun n ↦ (Q : ∀ n, Matrix (X n) (X n) ℂ) n ≠ 0) k)).rank

theorem manuscriptSentence_retainedCoordinatesAndRanks :
    PrintedRetainedCoordinatesAndRanks := by
  intro X _ Q q hQ hQmk hqne
  have hinf : {n : ℕ | (Q : ∀ n, Matrix (X n) (X n) ℂ) n ≠ 0}.Infinite :=
    CentralCoronaCornerPrintedRoute.manuscriptSentence_retainedCoordinatesInfinite
      X Q hQmk hqne
  refine ⟨hinf, Nat.nth_strictMono hinf, Nat.range_nth_of_infinite hinf, fun k ↦ ?_⟩
  have hne := Nat.nth_mem_of_infinite hinf k
  set n := Nat.nth (fun n ↦ (Q : ∀ n, Matrix (X n) (X n) ℂ) n ≠ 0) k with hn
  refine ⟨hne, one_le_rank_of_ne_zero (hQ n).1 (hQ n).2 hne, ?_⟩
  exact card_cornerPredicate_eq_rank (hQ n).1 (hQ n).2

end

end NonMFSentences
end Manuscript
end GroupApproximation

open GroupApproximation

#audit_closed_axioms
  Manuscript.NonMFSentences.card_cornerPredicate_eq_rank
#audit_closed_axioms
  Manuscript.NonMFSentences.manuscriptSentence_retainedCoordinatesAndRanks
