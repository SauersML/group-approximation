import GroupApproximation.Analysis.TracialMatrixUltraproduct
import GroupApproximation.Analysis.HilbertSchmidtApproximateUnit
import GroupApproximation.Analysis.TracialQuotientCStarIdentity

/-!
# The tracial matrix quotient is a C⋆-algebra

`Analysis/TracialMatrixUltraproduct` builds `TracialMatrixQuotient X l` as
`ℓ∞(Mₖ(ℂ)) ⧸ J`, where `J` is the ideal of `‖·‖₂`-null sequences, and equips it
with everything except the C⋆-identity: a `NormedRing`, a `StarRing`, a
`NormedStarGroup`, and completeness.  Its docstring says plainly that the
identity is not claimed, and why — the quotient norm here is a genuine
infimum, not the coordinatewise `limω ‖aₙ‖` of the operator-norm corona, so no
coordinatewise computation reaches it.

This file supplies the missing identity.  Nothing in the pinned mathlib does:
the complete list of `CStarRing` instances there contains no quotient
construction, and `Analysis/CStarAlgebra/` mentions `Ideal.Quotient` nowhere.
So this is the standard theorem — a quotient of a C⋆-algebra by a closed
two-sided `⋆`-ideal is a C⋆-algebra — and not an instantiation.

## What the proof needs, and what it does not

The standard proof runs through an approximate unit of the ideal.  It does
**not** need a genuine approximate-unit *net*: everything below uses only a
per-`j`, per-`ε` witness,

> for `j ∈ J` and `ε > 0` there is `e ∈ J` with `‖1 - e‖ ≤ 1` and
> `‖j - j e‖ ≤ ε`,

which is `exists_ideal_approximate_unit`.  Its coordinates come from
`HilbertSchmidtApproximateUnit.exists_projection_approximate_unit`, whose two
clauses are exactly the two things a witness has to do.  The first,
`‖jₙ - jₙ eₙ‖² ≤ t`, is the approximate-unit clause and is uniform in `n`, so
it survives the supremum defining the `ℓ∞` norm.  The second,
`t · ‖eₙ‖₂² ≤ ‖jₙ‖₂²`, is what keeps `e` *inside* `J`: the threshold `t` is
fixed before the sequence varies, so `‖jₙ‖₂ → 0` forces `‖eₙ‖₂ → 0`.

The earlier draft of the ambient docstring proposed the resolvent
`e = a (δ + a)⁻¹` instead, on the ground that the spectral projection is a
discontinuous function of `a` and would need the spectral theorem
coordinatewise.  That objection is real for a general C⋆-algebra and is void
here: the coordinates are *finite matrices*, where the spectral theorem is
`Matrix.IsHermitian.spectral_theorem` and is already available.  The
projection route is therefore the cheaper one in this setting, and it is the
one taken.

## The two steps

Writing `mk` for the quotient map, and using that `a e ∈ J` whenever `e ∈ J`:

* `‖mk a‖ ≤ ‖a (1 - e)‖` for every `e ∈ J`, because `a` and `a (1 - e)` differ
  by `a e ∈ J`.  This replaces the usual formula
  `‖mk a‖ = inf { ‖a (1 - e)‖ : e ∈ J, 0 ≤ e ≤ 1 }`; only the inequality is
  used, so the infimum is never formed and no `sInf` API is involved.
* `‖a (1 - e)‖² = ‖(1 - e) a⋆a (1 - e)‖ ≤ ‖a⋆a (1 - e)‖`, by the C⋆-identity in
  the *ambient* algebra together with `‖1 - e‖ ≤ 1`.  Choosing `e` for a nearly
  minimal representative `m` of `mk (a⋆a)` turns the right side into
  `‖mk (a⋆a)‖` up to the tolerance.

Only `‖x‖ * ‖x‖ ≤ ‖x⋆ x‖` is proved, because that is mathlib's single
`CStarRing` field; the reverse inequality is submultiplicativity plus the
isometric involution, and mathlib derives it.

## What sits on top of the identity

With the `CStarRing` field discharged, the file assembles the bundled
`CStarAlgebra` instance — every other field is an instance already installed
by `Analysis/TracialMatrixUltraproduct` — and states the identity in its
two-sided equational form `‖x⋆ x‖ = ‖x‖ * ‖x‖`.  It then records the
classical approximate-unit formula that the two steps above deliberately
avoided forming,

> `‖a + J‖ = inf { ‖a - a e‖ : e ∈ J }`   (`norm_mk_eq_sInf`),

whose `≥` half is `exists_ideal_approximate_unit` applied to the difference
`m - a ∈ J` of a nearly minimal representative `m`, and whose `≤` half needs
no approximate unit at all: `a e ∈ J`, so every `a - a e` represents the
class of `a`.

The hard direction is proved in
`Analysis/TracialQuotientCStarIdentity.lean` (the coordinatewise-cut API),
which this file imports; the instances are declared only here.
-/


open Filter Matrix
open scoped Matrix.Norms.L2Operator

namespace GroupApproximation
namespace TracialQuotientCStar

open TracialUltraproduct

noncomputable section

/-! ## Complements of projections are projections -/

/-- If `P` is an orthogonal projection then so is `1 - P`; hence `‖1 - P‖ ≤ 1`,
which is the only property of the approximate unit the estimates below use. -/
theorem isOrthogonalProjectionMatrix_one_sub {Y : Type*} [Fintype Y]
    [DecidableEq Y] {P : Matrix Y Y ℂ}
    (hP : KazhdanCornerMatrices.IsOrthogonalProjectionMatrix P) :
    KazhdanCornerMatrices.IsOrthogonalProjectionMatrix (1 - P) := by
  obtain ⟨hherm, hidem⟩ := hP
  constructor
  · rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hherm]
  · rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul,
      Matrix.mul_one, Matrix.one_mul, hidem]
    abel

/-- The complement of an orthogonal projection is a contraction. -/
theorem norm_one_sub_le_one {Y : Type*} [Fintype Y] [DecidableEq Y]
    {P : Matrix Y Y ℂ}
    (hP : KazhdanCornerMatrices.IsOrthogonalProjectionMatrix P) :
    ‖(1 : Matrix Y Y ℂ) - P‖ ≤ 1 :=
  ExactInvolutionLifts.norm_le_one_of_isOrthogonalProjection
    (isOrthogonalProjectionMatrix_one_sub hP)

/-! ## The approximate unit of the null ideal -/

variable (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)] (l : Filter ℕ)

/-- **The approximate-unit witness, one element and one tolerance at a time.**

This is all the approximate-unit theory the C⋆-identity needs: no net, no
directed system, no non-unital C⋆-structure on the ideal.  The witness is the
sequence of spectral cuts of `jₙᴴ jₙ`, assembled coordinatewise.

`‖1 - e‖ ≤ 1` stands in for the usual `0 ≤ e ≤ 1`: the estimates only ever use
the complement as a contraction, and each coordinate of `e` is an orthogonal
projection, so its complement is one too. -/
theorem exists_ideal_approximate_unit (j : ModelBoundedSequence X)
    (hj : IsHilbertSchmidtNull X l j) {ε : ℝ} (hε : 0 < ε) :
    ∃ e : ModelBoundedSequence X, IsHilbertSchmidtNull X l e ∧
      ‖(1 : ModelBoundedSequence X) - e‖ ≤ 1 ∧ ‖j - j * e‖ ≤ ε := by
  have ht : (0 : ℝ) < ε * ε := mul_pos hε hε
  -- One spectral cut per coordinate, at the threshold `ε²` fixed before `n`.
  choose f hproj _hfnorm hmove hhs using fun n : ℕ ↦
    HilbertSchmidtApproximateUnit.exists_projection_approximate_unit
      (X n) (j n) ht Fintype.card_pos
  have hfle : ∀ n, ‖f n‖ ≤ 1 := fun n ↦
    ExactInvolutionLifts.norm_le_one_of_isOrthogonalProjection (hproj n)
  obtain ⟨e, hecoe⟩ : ∃ e : ModelBoundedSequence X, ∀ n, e n = f n :=
    ⟨⟨f, memℓp_infty ⟨1, by rintro _ ⟨n, rfl⟩; exact hfle n⟩⟩, fun _ ↦ rfl⟩
  refine ⟨e, ?_, ?_, ?_⟩
  · -- `e ∈ J`: the second clause, divided through by the fixed threshold.
    refine isHilbertSchmidtNull_of_sq_le X l
      (g := fun n ↦ hsNormSq (X n) (j n) / (ε * ε)) ?_ ?_
    · have hjsq : Tendsto (fun n ↦ hsNormSq (X n) (j n)) l (nhds 0) :=
        (isHilbertSchmidtNull_iff_sq X l j).mp hj
      simpa using hjsq.div_const (ε * ε)
    · intro n
      rw [hecoe n, le_div_iff₀ ht, mul_comm]
      exact hhs n
  · -- `‖1 - e‖ ≤ 1`, coordinatewise, because each coordinate is a projection.
    refine lp.norm_le_of_forall_le zero_le_one fun n ↦ ?_
    have hcoord : ((1 : ModelBoundedSequence X) - e) n
        = (1 : Matrix (X n) (X n) ℂ) - f n := by
      simp only [lp.coeFn_sub, Pi.sub_apply, lp.infty_coeFn_one, Pi.one_apply,
        hecoe]
    rw [hcoord]
    exact norm_one_sub_le_one (hproj n)
  · -- `‖j - j e‖ ≤ ε`, uniformly in `n`, from the first clause.
    refine lp.norm_le_of_forall_le hε.le fun n ↦ ?_
    have hcoord : (j - j * e) n = j n - j n * f n := by
      simp only [lp.coeFn_sub, Pi.sub_apply, lp.infty_coeFn_mul, Pi.mul_apply,
        hecoe]
    rw [hcoord]
    have h := hmove n
    nlinarith [norm_nonneg (j n - j n * f n), hε]

/-! ## The C⋆-identity -/

-- No budget is raised for the declaration below.  It used to be: the
-- quotient's algebraic structure is assembled through three layers
-- (`lp` → `BoundedMatrixSequence` → `Submodule.Quotient`), and while
-- `TracialMatrixQuotient` was reducible, resolving `*`, `star` and `‖·‖` on it
-- re-walked all three every time.  It is opaque now and names its own
-- instances, so each of those goals is one step.
/-- **The C⋆-identity for the tracial matrix quotient.**

Only `‖x‖² ≤ ‖x⋆ x‖` is proved: it is mathlib's sole `CStarRing` field, and the
reverse inequality is `‖x⋆ x‖ ≤ ‖x⋆‖ ‖x‖ = ‖x‖²`, which mathlib derives from
submultiplicativity and the isometric involution the quotient already has. -/
theorem norm_mul_self_le_norm_star_mul (x : TracialMatrixQuotient X l) :
    ‖x‖ * ‖x‖ ≤ ‖star x * x‖ :=
  TracialUltraproduct.norm_sq_le_norm_star_mul_self X l x

/-- **The tracial matrix quotient satisfies the C⋆-identity.**

A `Prop`-valued mixin over the normed structure already installed in
`Analysis/TracialMatrixUltraproduct`: `CStarRing` carries no data, so this
cannot introduce a second norm and every lemma already stated against the
existing quotient norm keeps its meaning. -/
instance tracialMatrixQuotientCStarRing :
    CStarRing (TracialMatrixQuotient X l) where
  norm_mul_self_le := norm_mul_self_le_norm_star_mul X l

/-- **The tracial matrix quotient is a C⋆-algebra.**

Assembled entirely from instances that already exist -- the `NormedRing`,
`StarRing`, `CompleteSpace`, `NormedAlgebra ℂ` and `StarModule ℂ` of
`Analysis/TracialMatrixUltraproduct`, plus the mixin above.  Nothing here
constructs a norm, which is the point: `maximalGroupCStar_existsUnique_lift`
needs `[CStarAlgebra B]` on its target, and it must be *this* target, carrying
the norm the rest of the development is stated against. -/
noncomputable instance tracialMatrixQuotientCStarAlgebra :
    CStarAlgebra (TracialMatrixQuotient X l) :=
  -- The two `Star`-side parents are named rather than left to the structure
  -- elaborator.  Each resolves on its own -- `#synth` finds all seven parents
  -- -- but with `TracialMatrixQuotient` opaque the no-fields `where` no longer
  -- assembles them, reporting `star_add` and `norm_mul_self_le` as missing.
  -- Naming them changes nothing about which instances are used.
  { tracialMatrixQuotientStarRing X l,
    tracialMatrixQuotientCStarRing X l,
    tracialMatrixQuotientStarModule X l with }

/-- The C⋆-identity of the quotient in its two-sided, equational form.  The
`CStarRing` field carries only `‖x‖ * ‖x‖ ≤ ‖x⋆ x‖`; mathlib assembles the
reverse from submultiplicativity and the isometric involution, and this
records the equality once so downstream files need not repeat the assembly. -/
theorem norm_tracialMatrixQuotient_star_mul_self
    (x : TracialMatrixQuotient X l) : ‖star x * x‖ = ‖x‖ * ‖x‖ :=
  CStarRing.norm_star_mul_self

/-! ## The quotient norm as an infimum -/

/-- **The approximate-unit formula for the quotient norm**:
`‖a + J‖ = inf { ‖a - a e‖ : e ∈ J }`.

"The two steps" above deliberately used only one inequality of this formula,
so the infimum was never formed; with `exists_ideal_approximate_unit` in hand
the exact formula costs one more application of the same witness.  The `≤`
direction needs no approximate unit at all: `a e ∈ J`, so every `a - a e`
represents the class of `a`.  For `≥`, the witness is chosen for the
difference `m - a ∈ J` of a nearly minimal representative `m`, and with
`‖(m - a) - (m - a) e‖ ≤ ε/2` and `‖1 - e‖ ≤ 1`,

`‖a - a e‖ = ‖m (1 - e) - ((m - a) - (m - a) e)‖ ≤ ‖m‖ + ε/2 ≤ ‖a + J‖ + ε`.

The set is indexed by the whole ideal, with no positivity or contraction
constraint on `e`.  The constrained and unconstrained infima agree: dropping
constraints only enlarges the set, and an enlarged set can only lower an
infimum that the `≤` direction already bounds below by `‖a + J‖`. -/
theorem norm_mk_eq_sInf (a : ModelBoundedSequence X) :
    ‖tracialMatrixQuotientMk X l a‖ =
      sInf ((fun e ↦ ‖a - a * e‖) ''
        (hilbertSchmidtNullIdeal X l : Set (ModelBoundedSequence X))) := by
  refine le_antisymm ?_ ?_
  · -- `‖mk a‖` is a lower bound: each `a - a e` represents the class of `a`.
    refine le_csInf
      ⟨‖a - a * 0‖, 0, SetLike.mem_coe.mpr (Submodule.zero_mem _), rfl⟩ ?_
    rintro b ⟨e, he, rfl⟩
    have hae : tracialMatrixQuotientMk X l (a - a * e)
        = tracialMatrixQuotientMk X l a := by
      rw [map_sub, (tracialMatrixQuotientMk_eq_zero_iff_mem X l _).mpr
        ((mem_hilbertSchmidtNullIdeal_iff X l _).mpr
          (IsHilbertSchmidtNull.mul_left X l a
            ((mem_hilbertSchmidtNullIdeal_iff X l e).mp
              (SetLike.mem_coe.mp he)))), sub_zero]
    rw [← hae]
    exact tracialQuot_norm_mk_le X l _
  · -- The approximate unit brings an element of the set within any `ε`.
    have hbdd : BddBelow ((fun e ↦ ‖a - a * e‖) ''
        (hilbertSchmidtNullIdeal X l : Set (ModelBoundedSequence X))) := by
      refine ⟨0, ?_⟩
      rintro b ⟨e, -, rfl⟩
      exact norm_nonneg _
    refine le_of_forall_pos_le_add fun ε hε ↦ ?_
    have hδ : (0 : ℝ) < ε / 2 := by positivity
    -- A representative of `mk a` of nearly minimal norm, and the witness for
    -- its difference from `a`.
    obtain ⟨m, hm_eq, hm_lt⟩ := tracialQuot_exists_rep_norm_lt X l
      (tracialMatrixQuotientMk X l a) hδ
    have hj_mem : IsHilbertSchmidtNull X l (m - a) := by
      rw [← mem_hilbertSchmidtNullIdeal_iff,
        ← tracialMatrixQuotientMk_eq_zero_iff_mem X l, map_sub]
      exact sub_eq_zero.mpr hm_eq
    obtain ⟨e, he_mem, he_one_sub, he_move⟩ :=
      exists_ideal_approximate_unit X l (m - a) hj_mem hδ
    have hsInf_le := csInf_le hbdd
      (⟨e, SetLike.mem_coe.mpr
          ((mem_hilbertSchmidtNullIdeal_iff X l e).mpr he_mem), rfl⟩ :
        ‖a - a * e‖ ∈ (fun e ↦ ‖a - a * e‖) ''
          (hilbertSchmidtNullIdeal X l : Set (ModelBoundedSequence X)))
    have hkey : ‖a - a * e‖ ≤ ‖m‖ + ε / 2 := by
      have hsplit : a - a * e
          = m * ((1 : ModelBoundedSequence X) - e)
            - ((m - a) - (m - a) * e) := by
        simp only [mul_sub, sub_mul, mul_one]
        abel
      calc ‖a - a * e‖
          = ‖m * ((1 : ModelBoundedSequence X) - e)
              - ((m - a) - (m - a) * e)‖ := by rw [hsplit]
        _ ≤ ‖m * ((1 : ModelBoundedSequence X) - e)‖
              + ‖(m - a) - (m - a) * e‖ := norm_sub_le _ _
        _ ≤ ‖m‖ * ‖(1 : ModelBoundedSequence X) - e‖
              + ‖(m - a) - (m - a) * e‖ :=
            add_le_add (norm_mul_le _ _) le_rfl
        _ ≤ ‖m‖ * 1 + ε / 2 :=
            add_le_add
              (mul_le_mul_of_nonneg_left he_one_sub (norm_nonneg m)) he_move
        _ = ‖m‖ + ε / 2 := by rw [mul_one]
    linarith

end

end TracialQuotientCStar
end GroupApproximation
