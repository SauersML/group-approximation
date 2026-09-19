import GroupApproximation.Sofic.HilbertUltraproductSeparating

/-!
# `B_ω`, and its faithful action on `K_ω`

This is manuscript step KT.03 as printed, together with KT.04:

> form the norm ultraproduct `B_ω = ∏_ω B(K_n)` acting on `K_ω`; the action of
> `B_ω` on `K_ω` is faithful.

Until now the development substituted the *cofinite* corona `ℓ∞/c₀` for
`∏_ω B(K_n)`, and `Sofic/UltraproductAdjointAmbient.lean` said so in its own
header: the cofinite corona does **not** act faithfully on `K_ω`, because a
sequence that is null along `ω` but not cofinitely is a nonzero cofinite class
acting as zero.  With the corona construction now carrying its filter
(`Analysis/NormMatrixCorona.lean`), the printed object is available directly,
and on it the printed statement is true.

## What this file adds

* `OmegaAdjointCorona` -- `B_ω` itself, a complete complex C-star algebra,
  with `‖[A_n]_ω‖ = lim_ω ‖A_n‖` (`norm_omegaMk`);
* `omegaAct` -- the action of `B_ω` on `K_ω`, obtained by factoring the
  coordinatewise action through the `ω`-null ideal;
* `omegaAct_injective` -- KT.04: that action is faithful;
* `range_le_iff_mul_eq` -- KT.08 / NEW.UF.03: for idempotents, range inclusion
  in `K_ω` *is* the algebraic projection order;
* `ofCofinite_surjective` -- the comparison map, which exhibits the
  development's cofinite corona as a C-star algebra *surjecting onto* `B_ω`
  rather than equal to it.  This is the exact shape of the substitution the
  audit recorded, now a theorem rather than a caveat.

`B_ω` is introduced as an opaque type synonym with explicitly transported
structures, for the same reason `NormMatrixCStarCorona` is: exposing the raw
ideal quotient to typeclass search makes Lean unfold the noncommutative
quotient on every instance goal, which is not a budget problem to be raised
but a search that should not be started.
-/

namespace GroupApproximation
namespace OmegaOperatorUltraproduct

open Filter Matrix Topology
open UltrafilterLimit UltraproductModelConstruction
open HilbertUltraproductSeparating
open scoped Matrix.Norms.L2Operator

noncomputable section

variable (Y : ℕ → FiniteModel) [∀ n, Nonempty (Y n)] (w : ℕ → ℝ)
  (ω : Ultrafilter ℕ)

/-! ## KT.03: the algebra -/

/-- **KT.03, as printed.**  The manuscript's `B_ω = ∏_ω B(K_n)`: the norm
ultraproduct of the operator algebras of the `K_n` along the free ultrafilter
`ω`, exposed behind an opaque boundary so its intended structures elaborate
without unfolding the ideal quotient. -/
def OmegaAdjointCorona : Type :=
  FilterMatrixCoronaAlgebra (DblIdx Y) (ω : Filter ℕ)

noncomputable instance omegaAdjointCoronaNormedRing :
    NormedRing (OmegaAdjointCorona Y ω) := by
  unfold OmegaAdjointCorona
  exact filterMatrixCoronaAlgebraNormedRing (DblIdx Y) (ω : Filter ℕ)

noncomputable instance omegaAdjointCoronaCompleteSpace :
    CompleteSpace (OmegaAdjointCorona Y ω) := by
  unfold OmegaAdjointCorona
  exact filterMatrixCoronaAlgebraCompleteSpace (DblIdx Y) (ω : Filter ℕ)

noncomputable instance omegaAdjointCoronaStarRing :
    StarRing (OmegaAdjointCorona Y ω) := by
  unfold OmegaAdjointCorona
  exact filterMatrixCoronaAlgebraStarRing (DblIdx Y) (ω : Filter ℕ)

noncomputable instance omegaAdjointCoronaNormedStarGroup :
    NormedStarGroup (OmegaAdjointCorona Y ω) := by
  unfold OmegaAdjointCorona
  exact filterMatrixCoronaAlgebraNormedStarGroup (DblIdx Y) (ω : Filter ℕ)

noncomputable instance omegaAdjointCoronaCStarRing :
    CStarRing (OmegaAdjointCorona Y ω) := by
  unfold OmegaAdjointCorona
  exact filterMatrixCoronaAlgebraCStarRing (DblIdx Y) (ω : Filter ℕ)

noncomputable instance omegaAdjointCoronaAlgebra :
    Algebra ℂ (OmegaAdjointCorona Y ω) := by
  unfold OmegaAdjointCorona
  exact Ideal.Quotient.algebra ℂ

noncomputable instance omegaAdjointCoronaNormedAlgebra :
    NormedAlgebra ℂ (OmegaAdjointCorona Y ω) := by
  unfold OmegaAdjointCorona
  exact filterMatrixCoronaAlgebraNormedAlgebra (DblIdx Y) (ω : Filter ℕ)

noncomputable instance omegaAdjointCoronaStarModule :
    StarModule ℂ (OmegaAdjointCorona Y ω) := by
  unfold OmegaAdjointCorona
  exact filterMatrixCoronaAlgebraStarModule (DblIdx Y) (ω : Filter ℕ)

/-- `B_ω` carries mathlib's bundled unital complex C-star-algebra structure.
This is the sense in which the manuscript's "norm ultraproduct" is an object
of the theory and not a notation. -/
noncomputable instance omegaAdjointCoronaCStarAlgebra :
    CStarAlgebra (OmegaAdjointCorona Y ω) where
  toNormedRing := omegaAdjointCoronaNormedRing Y ω
  toStarRing := omegaAdjointCoronaStarRing Y ω
  toCompleteSpace := omegaAdjointCoronaCompleteSpace Y ω
  toCStarRing := omegaAdjointCoronaCStarRing Y ω
  toNormedAlgebra := omegaAdjointCoronaNormedAlgebra Y ω
  toStarModule := omegaAdjointCoronaStarModule Y ω

/-- The quotient map `[·]_ω` onto `B_ω`. -/
def omegaMk :
    BoundedMatrixSequence (DblIdx Y) →+* OmegaAdjointCorona Y ω := by
  unfold OmegaAdjointCorona
  exact filterMatrixCoronaMk (DblIdx Y) (ω : Filter ℕ)

theorem omegaMk_surjective : Function.Surjective (omegaMk Y ω) := by
  unfold omegaMk OmegaAdjointCorona
  exact Ideal.Quotient.mk_surjective

theorem omegaMk_eq_zero_iff (a : BoundedMatrixSequence (DblIdx Y)) :
    omegaMk Y ω a = 0 ↔
      Tendsto (fun n ↦ ‖(a : ∀ n, Matrix (DblIdx Y n) (DblIdx Y n) ℂ) n‖)
        (ω : Filter ℕ) (𝓝 0) :=
  filterMatrixCoronaMk_eq_zero_iff (DblIdx Y) (ω : Filter ℕ) a

/-- **The norm of `B_ω` is the ultralimit of the coordinate norms.**  For a
general filter the corona norm is a limsup; along an ultrafilter a bounded
real sequence converges, so the limsup is the manuscript's `lim_ω ‖A_n‖`. -/
theorem norm_omegaMk (a : BoundedMatrixSequence (DblIdx Y)) :
    ‖omegaMk Y ω a‖ =
      ulim ω (fun n ↦ ‖(a : ∀ n, Matrix (DblIdx Y n) (DblIdx Y n) ℂ) n‖) := by
  obtain ⟨L, hL⟩ :
      ∃ L : ℝ, Tendsto
        (fun n ↦ ‖(a : ∀ n, Matrix (DblIdx Y n) (DblIdx Y n) ℂ) n‖)
        (ω : Filter ℕ) (𝓝 L) :=
    exists_tendsto_of_bounded (C := ‖a‖) ω fun n ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      exact boundedMatrixSequence_coord_norm_le (DblIdx Y) a n
  have hgen : ‖filterMatrixCoronaMk (DblIdx Y) (ω : Filter ℕ) a‖ = L := by
    rw [filterMatrixCoronaMk_apply,
      norm_filterMatrixCorona_mk_eq_limsup (DblIdx Y) (ω : Filter ℕ) a]
    exact hL.limsup_eq
  rw [ulim_eq hL]
  exact hgen

/-! ## KT.04: the faithful action -/

/-- The coordinatewise action of an operator sequence on `K_ω`, packaged as a
ring homomorphism so that it can be factored through the `ω`-null ideal. -/
def actRing :
    BoundedMatrixSequence (DblIdx Y) →+* Module.End ℂ (Vec Y w ω) where
  toFun := actQ Y w ω
  map_one' := actQ_one Y w ω
  map_mul' a b := actQ_mul Y w ω a b
  map_zero' := actQ_zero Y w ω
  map_add' a b := actQ_add Y w ω a b

@[simp] theorem actRing_apply (a : BoundedMatrixSequence (DblIdx Y)) :
    actRing Y w ω a = actQ Y w ω a := rfl

/-- **KT.03, the action.**  The coordinatewise action kills the `ω`-null
sequences, so it descends to `B_ω`.  This is the step the development
previously performed on the cofinite corona, where it is well defined but not
faithful. -/
def omegaAct (hw : ∀ n, 0 ≤ w n) :
    OmegaAdjointCorona Y ω →+* Module.End ℂ (Vec Y w ω) := by
  unfold OmegaAdjointCorona
  exact Ideal.Quotient.lift (nullMatrixSequenceIdeal (DblIdx Y) (ω : Filter ℕ))
    (actRing Y w ω)
    fun a ha ↦ HilbertUltraproductFaithful.act_eq_zero_of_omegaNull hw a ha

@[simp] theorem omegaAct_omegaMk (hw : ∀ n, 0 ≤ w n)
    (a : BoundedMatrixSequence (DblIdx Y)) :
    omegaAct Y w ω hw (omegaMk Y ω a) = actQ Y w ω a := rfl

/-- **KT.04, as printed.**  The action of `B_ω` on `K_ω` is faithful.

The manuscript's justification is exactly the one used here: a nonzero class
has `lim_ω ‖A_n‖ = δ > 0`, and test vectors nearly attaining the coordinate
norms exhibit a vector of `K_ω` that the class does not annihilate.  On the
cofinite corona the same statement is false, which is why this could not be
recorded before the corona carried its filter. -/
theorem omegaAct_injective (hw : ∀ n, 0 < w n) :
    Function.Injective (omegaAct Y w ω (fun n ↦ (hw n).le)) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨a, rfl⟩ := omegaMk_surjective Y ω x
  rw [omegaAct_omegaMk] at hx
  rw [omegaMk_eq_zero_iff]
  exact (actQ_eq_zero_iff_tendsto hw a).1 hx

/-! ## KT.08: the projection order, read off the faithful action -/

/-- **KT.08 / NEW.UF.03, the printed direction.**  For an idempotent `q` of
`B_ω`, an inclusion of *ranges in `K_ω`* forces the algebraic identity
`q p = p`.

This is the step the manuscript draws from faithfulness: "for projections
`P, Q ∈ B_ω` the inclusion `ran P ⊆ ran Q` makes `QP` and `P` act identically
on `K_ω`, so `QP = P`, that is, `P ≤ Q`".  The development previously recorded
only the algebraic surrogate `(1-q)p = 0 → qp = p`, whose hypothesis is the
conclusion written differently; the range inclusion is what the printed proof
actually has in hand. -/
theorem mul_eq_of_range_le (hw : ∀ n, 0 < w n)
    {p q : OmegaAdjointCorona Y ω} (hq : q * q = q)
    (hle : LinearMap.range (omegaAct Y w ω (fun n ↦ (hw n).le) p)
      ≤ LinearMap.range (omegaAct Y w ω (fun n ↦ (hw n).le) q)) :
    q * p = p := by
  have hqq : omegaAct Y w ω (fun n ↦ (hw n).le) q *
      omegaAct Y w ω (fun n ↦ (hw n).le) q
      = omegaAct Y w ω (fun n ↦ (hw n).le) q := by
    rw [← map_mul, hq]
  refine omegaAct_injective Y w ω hw ?_
  rw [map_mul]
  refine LinearMap.ext fun x ↦ ?_
  obtain ⟨y, hy⟩ := hle ⟨x, rfl⟩
  calc (omegaAct Y w ω (fun n ↦ (hw n).le) q *
          omegaAct Y w ω (fun n ↦ (hw n).le) p) x
      = omegaAct Y w ω (fun n ↦ (hw n).le) q
          (omegaAct Y w ω (fun n ↦ (hw n).le) p x) := rfl
    _ = omegaAct Y w ω (fun n ↦ (hw n).le) q
          (omegaAct Y w ω (fun n ↦ (hw n).le) q y) := by rw [hy]
    _ = (omegaAct Y w ω (fun n ↦ (hw n).le) q *
          omegaAct Y w ω (fun n ↦ (hw n).le) q) y := rfl
    _ = omegaAct Y w ω (fun n ↦ (hw n).le) q y := by rw [hqq]
    _ = omegaAct Y w ω (fun n ↦ (hw n).le) p x := hy

/-- The converse, which the manuscript calls immediate: the algebraic order
gives the range inclusion. -/
theorem range_le_of_mul_eq (hw : ∀ n, 0 < w n)
    {p q : OmegaAdjointCorona Y ω} (h : q * p = p) :
    LinearMap.range (omegaAct Y w ω (fun n ↦ (hw n).le) p)
      ≤ LinearMap.range (omegaAct Y w ω (fun n ↦ (hw n).le) q) := by
  have hqp : omegaAct Y w ω (fun n ↦ (hw n).le) q *
      omegaAct Y w ω (fun n ↦ (hw n).le) p
      = omegaAct Y w ω (fun n ↦ (hw n).le) p := by
    rw [← map_mul, h]
  rintro z ⟨x, rfl⟩
  refine ⟨omegaAct Y w ω (fun n ↦ (hw n).le) p x, ?_⟩
  calc omegaAct Y w ω (fun n ↦ (hw n).le) q
        (omegaAct Y w ω (fun n ↦ (hw n).le) p x)
      = (omegaAct Y w ω (fun n ↦ (hw n).le) q *
          omegaAct Y w ω (fun n ↦ (hw n).le) p) x := rfl
    _ = omegaAct Y w ω (fun n ↦ (hw n).le) p x := by rw [hqp]

/-- **NEW.UF.03.**  For idempotents of `B_ω`, range inclusion in `K_ω` and the
algebraic projection order are the same relation. -/
theorem range_le_iff_mul_eq (hw : ∀ n, 0 < w n)
    {p q : OmegaAdjointCorona Y ω} (hq : q * q = q) :
    LinearMap.range (omegaAct Y w ω (fun n ↦ (hw n).le) p)
        ≤ LinearMap.range (omegaAct Y w ω (fun n ↦ (hw n).le) q) ↔
      q * p = p :=
  ⟨mul_eq_of_range_le Y w ω hw hq, range_le_of_mul_eq Y w ω hw⟩

/-! ## The cofinite corona as a surrogate, made precise -/

/-- A free ultrafilter lies below the cofinite filter, so every cofinitely
null sequence is `ω`-null and the cofinite corona maps onto `B_ω`. -/
def ofCofinite (hω : (ω : Filter ℕ) ≤ cofinite) :
    NormMatrixCStarCorona (DblIdx Y) →+* OmegaAdjointCorona Y ω := by
  unfold NormMatrixCStarCorona
  exact Ideal.Quotient.lift (nullMatrixSequenceIdeal (DblIdx Y) cofinite)
    (omegaMk Y ω)
    fun a ha ↦ (omegaMk_eq_zero_iff Y ω a).2
      (IsNullMatrixSequence.mono (DblIdx Y) cofinite hω ha)

@[simp] theorem ofCofinite_mk (hω : (ω : Filter ℕ) ≤ cofinite)
    (a : BoundedMatrixSequence (DblIdx Y)) :
    ofCofinite Y ω hω (normMatrixCStarCoronaMk (DblIdx Y) a) = omegaMk Y ω a :=
  rfl

/-- **The substitution the audit recorded, as a theorem.**  `B_ω` is a
quotient of the cofinite corona, not the same algebra: the comparison map is
onto, and its kernel is the classes that are cofinitely nonnull but `ω`-null.
Those are precisely the elements on which the cofinite action fails to be
faithful. -/
theorem ofCofinite_surjective (hω : (ω : Filter ℕ) ≤ cofinite) :
    Function.Surjective (ofCofinite Y ω hω) := by
  intro x
  obtain ⟨a, rfl⟩ := omegaMk_surjective Y ω x
  exact ⟨normMatrixCStarCoronaMk (DblIdx Y) a, ofCofinite_mk Y ω hω a⟩

end

end OmegaOperatorUltraproduct
end GroupApproximation
