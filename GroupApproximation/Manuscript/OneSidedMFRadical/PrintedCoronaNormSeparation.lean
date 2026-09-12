import GroupApproximation.Manuscript.OneSidedMFRadical.PrintedResidualCalculusProof

/-!
# The corona-norm separation retained by the printed stage choice

`non_mf_groups_exist.tex`, in the proof of
`\begin{proposition}[basic properties of the MF radical]`
`\label{prop:mf-residual-calculus}`:

> Choose each coordinate far enough out that the first `n` multiplication
> defects are at most `1/n` and the designated value at `x_j` retains at least
> half of its corona-norm separation.

## The gap this closes

`Manuscript/OneSidedMFRadical/PrintedResidualCalculusProof.lean` already
attaches `manuscriptPrintedStageDirectSum` to this sentence: the block sum of a
finite list of coordinate blocks is unitary, meets the printed `1/n`
multiplication tolerance, and retains the separation of the designated block --
the whole of it, and a fortiori the printed half.  Its docstring records what
that declaration does *not* say, and this module supplies exactly that:

> The constant retained is the separation of the chosen coordinate, and no
> arithmetic relation between it and a corona norm is asserted here.

The printed sentence asserts the relation.  The designated value lives in the
corona; its "corona-norm separation" is the quotient norm
`‖π(x_j) - 1‖`, a single real number attached to a *class*, whereas the block
sum retains a *coordinate* quantity `‖v_n - 1‖`.  What links them is the
quotient-norm identity for the norm-matrix corona: the norm of a class is the
`limsup` of the coordinate norms.  Because a `limsup` is not exceeded only
eventually but *approached* frequently, every real number strictly below the
corona norm is exceeded by the coordinate norms at coordinates arbitrarily far
out -- and `‖π(x_j) - 1‖ / 2` is such a number as soon as the separation is
positive.  That is the printed "such coordinates exist arbitrarily far out",
made quantitative at the printed constant `1/2`.

## What was already in the tree and what is new

`Analysis/NormMatrixCorona.lean` proves the identity at an arbitrary filter,
`norm_filterMatrixCorona_mk_eq_limsup`, and
`PrintedCoordinatesExistArbitrarilyFarOut` already carries its cofinite
instance as the second clause of printed sentence 8.  Nothing here reproves it.
What is new is

* `norm_normMatrixCStarCoronaMk_eq_limsup`, the same identity at the *public*
  opaque corona `NormMatrixCStarCorona` -- the object the manuscript's corona
  homomorphisms actually take values in, and the only form in which the
  identity can be applied to `π(x_j)`;
* the passage from the identity to a frequently-attained coordinate lower
  bound (`frequently_lt_coordNorm_of_lt_limsup`,
  `frequently_half_limsup_le_coordNorm`), and its "arbitrarily far out" form
  at any filter refining `atTop` -- which covers the cofinite corona and every
  free ultrafilter;
* `PrintedCoronaNormSeparation`, the printed sentence itself: given
  finite-dimensional unitary models with vanishing multiplicative defects, a
  designated element `x`, a finite set of multiplication tests and a stage
  `m`, there is a coordinate beyond any prescribed index at which every test
  is met at the printed tolerance `1/m` **and** the coordinate value retains
  at least half of the corona-norm separation `‖π(x) - 1‖` of the designated
  value.

Where the Lean is more explicit than the printed sentence, in the direction of
a stronger claim:

* the half-retention statements are unconditional -- no positivity of the
  corona-norm separation is assumed, because at separation zero the printed
  half is zero and every coordinate retains it;
* the "arbitrarily far out" lemmas are proved at any filter `l` with
  `l ≤ atTop`, not only at `cofinite`, so the same statements serve the
  ultraproduct corona of `thm:kazhdan-transport`;
* `frequently_lt_coordNorm_of_lt_limsup` is stated at an arbitrary threshold
  `c` below the corona norm; `1/2` is the printed instance, not the limit of
  the method.

No theorem from the literature is an input.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

open scoped Matrix.Norms.L2Operator

noncomputable section

universe u

/-! ## The corona norm is a limsup, at the public corona -/

/-- **The quotient-norm identity at the public cofinite corona.**  The norm of
the class of a bounded matrix sequence in `NormMatrixCStarCorona` is the
`limsup` of the coordinate operator norms along the cofinite filter.

`norm_filterMatrixCorona_mk_eq_limsup` proves this at the reducible quotient
`FilterMatrixCoronaAlgebra X l` for every `l` with `l.NeBot`.  The manuscript's
corona homomorphisms take values in the *opaque* type synonym
`NormMatrixCStarCorona`, whose structures are transported rather than inferred,
so the identity has to be restated there before it can be applied to a value
`π(x_j)`.  Both types have the same elements and the same transported norm, so
the transport is the identity. -/
theorem norm_normMatrixCStarCoronaMk_eq_limsup (Y : ℕ → Type u)
    [∀ n, Fintype (Y n)] [∀ n, DecidableEq (Y n)] [∀ n, Nonempty (Y n)]
    (a : BoundedMatrixSequence Y) :
    ‖normMatrixCStarCoronaMk Y a‖ =
      Filter.limsup (fun n ↦ ‖a n‖) Filter.cofinite := by
  unfold normMatrixCStarCoronaMk NormMatrixCStarCorona
  exact norm_filterMatrixCorona_mk_eq_limsup Y Filter.cofinite a

/-- **"the quotient norm is a limsup"**, the printed reason, as one closed
proposition: at every filter with `NeBot` the quotient norm of a class in the
matrix corona is the `limsup` of the coordinate operator norms, and the same
holds at the public cofinite corona `NormMatrixCStarCorona`.

The first clause is `norm_filterMatrixCorona_mk_eq_limsup`, which
`PrintedCoordinatesExistArbitrarilyFarOut` already carries at `cofinite`; it is
restated here at an arbitrary filter because it is the reusable ingredient of
the sentence closed below, and because the second clause -- the form the
printed `π(x_j)` needs -- is new. -/
def PrintedCoronaNormIsLimsup : Prop :=
  ∀ (Y : ℕ → Type) [∀ n, Fintype (Y n)] [∀ n, DecidableEq (Y n)]
      [∀ n, Nonempty (Y n)] (a : BoundedMatrixSequence Y),
    (∀ l : Filter ℕ, l.NeBot →
        ‖Ideal.Quotient.mk (nullMatrixSequenceIdeal Y l) a‖ =
          Filter.limsup (fun n ↦ ‖a n‖) l) ∧
      ‖normMatrixCStarCoronaMk Y a‖ =
        Filter.limsup (fun n ↦ ‖a n‖) Filter.cofinite

/-- Closed proof of the quotient-norm identity, at an arbitrary filter and at
the public cofinite corona. -/
theorem manuscriptPrintedCoronaNormIsLimsup : PrintedCoronaNormIsLimsup := by
  intro Y _ _ _ a
  refine ⟨fun l hl ↦ ?_, norm_normMatrixCStarCoronaMk_eq_limsup Y a⟩
  haveI := hl
  exact norm_filterMatrixCorona_mk_eq_limsup Y l a

/-! ## From the limsup to a coordinate lower bound

A `limsup` is not merely an eventual upper bound: every real number strictly
below it is exceeded *frequently*.  That is the whole content of "such
coordinates exist arbitrarily far out". -/

/-- The `limsup` of the coordinate operator norms is nonnegative.  Coordinate
norms are nonnegative and uniformly bounded by the `ℓ∞` norm of the sequence,
which is exactly what a `limsup` bound needs at both ends. -/
theorem limsup_coordNorm_nonneg (Y : ℕ → Type u) [∀ n, Fintype (Y n)]
    [∀ n, DecidableEq (Y n)] [∀ n, Nonempty (Y n)] (l : Filter ℕ)
    [Filter.NeBot l] (a : BoundedMatrixSequence Y) :
    0 ≤ Filter.limsup (fun n ↦ ‖a n‖) l :=
  Filter.le_limsup_of_frequently_le
    (Filter.Frequently.of_forall fun n ↦ norm_nonneg (a n))
    ⟨‖a‖, show ∀ᶠ n : ℕ in l, ‖a n‖ ≤ ‖a‖ from
      Filter.Eventually.of_forall fun n ↦
        boundedMatrixSequence_coord_norm_le Y a n⟩

/-- **Every threshold below the `limsup` is exceeded frequently.**  If
`c < limsup_l ‖a_n‖` then `c < ‖a_n‖` at the coordinates of a frequently
occurring set.

This is the exact converse of the eventual bound
`eventually_coordNorm_lt_of_corona_norm_lt`, and it is the direction the
printed choice uses: an eventual *upper* bound cannot produce a coordinate at
which the designated value is still large, but a `limsup` lower bound can. -/
theorem frequently_lt_coordNorm_of_lt_limsup (Y : ℕ → Type u)
    [∀ n, Fintype (Y n)] [∀ n, DecidableEq (Y n)] [∀ n, Nonempty (Y n)]
    (l : Filter ℕ) [Filter.NeBot l] (a : BoundedMatrixSequence Y) {c : ℝ}
    (hc : c < Filter.limsup (fun n ↦ ‖a n‖) l) :
    ∃ᶠ n in l, c < ‖a n‖ :=
  Filter.frequently_lt_of_lt_limsup
    (Filter.isCoboundedUnder_le_of_le l fun n ↦ norm_nonneg (a n)) hc

/-- **Half of the `limsup` is retained frequently.**  No positivity hypothesis:
when the `limsup` is zero its half is zero and every coordinate norm clears it,
and when it is positive its half is strictly below it, so the previous lemma
applies. -/
theorem frequently_half_limsup_le_coordNorm (Y : ℕ → Type u)
    [∀ n, Fintype (Y n)] [∀ n, DecidableEq (Y n)] [∀ n, Nonempty (Y n)]
    (l : Filter ℕ) [Filter.NeBot l] (a : BoundedMatrixSequence Y) :
    ∃ᶠ n in l, Filter.limsup (fun k ↦ ‖a k‖) l / 2 ≤ ‖a n‖ := by
  rcases (limsup_coordNorm_nonneg Y l a).lt_or_eq with hpos | hzero
  · refine (frequently_lt_coordNorm_of_lt_limsup Y l a
      (c := Filter.limsup (fun k ↦ ‖a k‖) l / 2) (by linarith)).mono ?_
    intro n hn
    exact hn.le
  · refine Filter.Frequently.of_forall fun n ↦ ?_
    rw [← hzero, zero_div]
    exact norm_nonneg (a n)

/-! ## "Such coordinates exist arbitrarily far out"

At any filter refining `atTop` -- the cofinite filter on `ℕ`, and every free
ultrafilter -- a frequently occurring set meets every tail, which is the
printed "arbitrarily far out". -/

/-- **A coordinate beyond any prescribed index at which the coordinate norm
exceeds any threshold below the corona norm.** -/
theorem exists_ge_lt_coordNorm_of_lt_coronaNorm (Y : ℕ → Type u)
    [∀ n, Fintype (Y n)] [∀ n, DecidableEq (Y n)] [∀ n, Nonempty (Y n)]
    (l : Filter ℕ) [Filter.NeBot l] (hl : l ≤ Filter.atTop)
    (a : BoundedMatrixSequence Y) {c : ℝ}
    (hc : c < ‖Ideal.Quotient.mk (nullMatrixSequenceIdeal Y l) a‖) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ c < ‖a n‖ := by
  have hfreq : ∃ᶠ n in l, c < ‖a n‖ := by
    refine frequently_lt_coordNorm_of_lt_limsup Y l a ?_
    rwa [norm_filterMatrixCorona_mk_eq_limsup Y l a] at hc
  obtain ⟨n, hcn, hNn⟩ :=
    (hfreq.and_eventually
      (Filter.Eventually.filter_mono hl (Filter.eventually_ge_atTop N))).exists
  exact ⟨n, hNn, hcn⟩

/-- **A coordinate beyond any prescribed index retaining at least half of the
corona norm.**  The printed constant, with no positivity hypothesis. -/
theorem exists_ge_half_coronaNorm_le_coordNorm (Y : ℕ → Type u)
    [∀ n, Fintype (Y n)] [∀ n, DecidableEq (Y n)] [∀ n, Nonempty (Y n)]
    (l : Filter ℕ) [Filter.NeBot l] (hl : l ≤ Filter.atTop)
    (a : BoundedMatrixSequence Y) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧
      ‖Ideal.Quotient.mk (nullMatrixSequenceIdeal Y l) a‖ / 2 ≤ ‖a n‖ := by
  have hfreq : ∃ᶠ n in l,
      ‖Ideal.Quotient.mk (nullMatrixSequenceIdeal Y l) a‖ / 2 ≤ ‖a n‖ := by
    rw [norm_filterMatrixCorona_mk_eq_limsup Y l a]
    exact frequently_half_limsup_le_coordNorm Y l a
  obtain ⟨n, hcn, hNn⟩ :=
    (hfreq.and_eventually
      (Filter.Eventually.filter_mono hl (Filter.eventually_ge_atTop N))).exists
  exact ⟨n, hNn, hcn⟩

/-! ## The designated value, at the printed objects

The printed `π(x_j)` is a unitary of the public corona and its coordinate lifts
are coordinatewise-unitary sequences, which is what
`manuscriptPrintedPolarCoordinateUnitaryLifts` supplies.  The next lemma says
the printed thing about that pair. -/

/-- **The class of a coordinatewise-unitary sequence, minus the identity, is
the class of the coordinatewise difference.**  Purely structural: the corona
map is a ring homomorphism and `ℓ∞` operations are coordinatewise. -/
theorem unitarySequenceToCorona_sub_one (X : ℕ → FiniteModel)
    [∀ n, Nonempty (X n)] (v : ∀ n, Matrix.unitaryGroup (X n) ℂ) :
    ((unitarySequenceToCorona X v :
          unitary (NormMatrixCStarCorona (fun k ↦ X k))) :
        NormMatrixCStarCorona (fun k ↦ X k)) - 1 =
      normMatrixCStarCoronaMk (fun k ↦ X k)
        (unitarySequenceBounded X v - 1) :=
  calc ((unitarySequenceToCorona X v :
          unitary (NormMatrixCStarCorona (fun k ↦ X k))) :
        NormMatrixCStarCorona (fun k ↦ X k)) - 1
      = normMatrixCStarCoronaMk (fun k ↦ X k)
          (unitarySequenceBounded X v) - 1 := rfl
    _ = normMatrixCStarCoronaMk (fun k ↦ X k) (unitarySequenceBounded X v) -
          normMatrixCStarCoronaMk (fun k ↦ X k) 1 := by rw [map_one]
    _ = normMatrixCStarCoronaMk (fun k ↦ X k)
          (unitarySequenceBounded X v - 1) := (map_sub _ _ _).symm

/-- **The printed retention, at the printed objects.**  For a
coordinatewise-unitary sequence `v` with class `π = [v]` in the public corona,
the coordinate separations `‖v_n - 1‖` retain at least half of the corona-norm
separation `‖π - 1‖` at coordinates arbitrarily far out.

This is the arithmetic link the printed sentence needs and that
`manuscriptPrintedStageDirectSum` explicitly does not assert: it converts the
corona-norm quantity `‖π - 1‖` into a *coordinate* constant `delta`, which is
the shape the block-sum retention clause consumes. -/
theorem frequently_half_coronaSeparation_le_coordSeparation
    (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]
    (v : ∀ n, Matrix.unitaryGroup (X n) ℂ) :
    ∃ᶠ n in Filter.atTop,
      ‖((unitarySequenceToCorona X v :
            unitary (NormMatrixCStarCorona (fun k ↦ X k))) :
          NormMatrixCStarCorona (fun k ↦ X k)) - 1‖ / 2 ≤
        ‖(v n : Matrix (X n) (X n) ℂ) - 1‖ := by
  rw [unitarySequenceToCorona_sub_one X v, ← Nat.cofinite_eq_atTop,
    norm_normMatrixCStarCoronaMk_eq_limsup (fun k ↦ X k)
      (unitarySequenceBounded X v - 1)]
  refine (frequently_half_limsup_le_coordNorm (fun k ↦ X k) Filter.cofinite
    (unitarySequenceBounded X v - 1)).mono ?_
  intro n hn
  exact hn

/-! ## The printed sentence -/

/-- **"Choose each coordinate far enough out that the first `n` multiplication
defects are at most `1/n` and the designated value at `x_j` retains at least
half of its corona-norm separation."**

Both clauses of the printed choice, at one coordinate beyond any prescribed
index: for finite-dimensional unitary models whose multiplicative defects tend
to zero in operator norm, a designated element `x`, a finite set `S` of
multiplication tests standing for "the first `n` multiplication defects", a
stage `m > 0` and a starting index `N`, there is a coordinate `n ≥ N` at which

* every test in `S` is met at the printed tolerance `1/m`, and
* the coordinate separation `‖V_n(x) - 1‖` is at least half of the corona-norm
  separation `‖π(x) - 1‖` of the designated value, where `π(x)` is the class of
  the coordinate sequence in the public corona.

The corona-norm separation appears literally, as the quotient norm of
`π(x) - 1` in `NormMatrixCStarCorona`; that is precisely what
`manuscriptPrintedStageDirectSum` leaves unrelated to the coordinate constant
it retains, and it is what the `limsup` identity supplies.

The retention clause carries no positivity hypothesis: at corona-norm
separation zero its half is zero and every coordinate retains it, so the
statement is the printed one with the vacuous case included rather than
excluded. -/
def PrintedCoronaNormSeparation : Prop :=
  ∀ (X : ℕ → FiniteModel) (hX : ∀ n, 0 < Fintype.card (X n)),
    letI : ∀ n, Nonempty (X n) := fun n ↦ Fintype.card_pos_iff.mp (hX n)
    ∀ (G : Type) [Group G] (V : ∀ n, G → Matrix.unitaryGroup (X n) ℂ),
      (∀ g h : G, ∀ eps : ℝ, 0 < eps → ∃ M, ∀ n ≥ M,
          ‖(V n (g * h) : Matrix (X n) (X n) ℂ) -
            (V n g : Matrix (X n) (X n) ℂ) * V n h‖ ≤ eps) →
        ∀ (x : G) (S : Finset (G × G)) (m N : ℕ), 0 < m →
          ∃ n : ℕ, N ≤ n ∧
            (∀ p ∈ S,
              ‖(V n (p.1 * p.2) : Matrix (X n) (X n) ℂ) -
                (V n p.1 : Matrix (X n) (X n) ℂ) * V n p.2‖ ≤ 1 / (m : ℝ)) ∧
            ‖((unitarySequenceToCorona X (fun k ↦ V k x) :
                  unitary (NormMatrixCStarCorona (fun k ↦ X k))) :
                NormMatrixCStarCorona (fun k ↦ X k)) - 1‖ / 2 ≤
              ‖(V n x : Matrix (X n) (X n) ℂ) - 1‖

/-- Closed proof of the printed sentence.  Finitely many eventual defect
bounds are eventually simultaneous; half the corona-norm separation is
retained frequently, by the `limsup` identity; a frequently occurring set meets
every tail of an eventually occurring one. -/
theorem manuscriptPrintedCoronaNormSeparation : PrintedCoronaNormSeparation := by
  intro X hX
  letI : ∀ n, Nonempty (X n) := fun n ↦ Fintype.card_pos_iff.mp (hX n)
  intro G _ V hmul x S m N hm
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hall : ∀ᶠ n in Filter.atTop, ∀ p ∈ S,
      ‖(V n (p.1 * p.2) : Matrix (X n) (X n) ℂ) -
        (V n p.1 : Matrix (X n) (X n) ℂ) * V n p.2‖ ≤ 1 / (m : ℝ) := by
    rw [Filter.eventually_all_finset]
    intro p _
    exact Filter.eventually_atTop.mpr
      (hmul p.1 p.2 (1 / (m : ℝ)) (one_div_pos.mpr hmR))
  have hsep := frequently_half_coronaSeparation_le_coordSeparation X
    (fun k ↦ V k x)
  obtain ⟨n, ⟨hs, hd⟩, hn⟩ :=
    ((hsep.and_eventually hall).and_eventually
      (Filter.eventually_ge_atTop N)).exists
  exact ⟨n, hn, hd, hs⟩

/-! ## The paragraph, assembled -/

/-- The printed sentence together with the quotient-norm identity that is its
printed reason, as one closed proposition. -/
def PrintedCoronaNormSeparationParagraph : Prop :=
  PrintedCoronaNormIsLimsup ∧ PrintedCoronaNormSeparation

/-- Closed proof of the printed sentence and its printed reason. -/
theorem manuscriptPrintedCoronaNormSeparationParagraph :
    PrintedCoronaNormSeparationParagraph :=
  ⟨manuscriptPrintedCoronaNormIsLimsup, manuscriptPrintedCoronaNormSeparation⟩

end

end OneSidedMFRadical
end Manuscript
end GroupApproximation
