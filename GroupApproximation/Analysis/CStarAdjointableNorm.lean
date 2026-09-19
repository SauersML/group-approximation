import GroupApproximation.Analysis.CStarHilbertModuleNorm

/-!
# The operator norm on `𝓛(E)`, and the C⋆-identity

`Analysis.CStarAdjointable` proves that an adjointable operator is
automatically additive, `ℂ`-linear and `B`-linear.  **Boundedness is the one
property that does not come for free that way**: the classical proof that an
adjointable operator on a Hilbert module is bounded is the closed graph
theorem, and it needs the module to be complete, which a bundled
`CStarModule` is not asked to be.  So boundedness is carried as a hypothesis
here --- `IsBoundedBy`, `IsBounded` --- and every operator this development
actually builds is proved bounded by hand.  Nothing is lost: rank-one
operators, finite-rank operators, and everything in `𝓚(E)` are bounded with
explicit constants.

## What is proved

* `sub`, `neg`, `map_sub` --- the difference of two adjointable operators,
  which is what "closure of the finite-rank operators" is stated with;
* `IsBoundedBy.adjoint` --- **an operator and its adjoint have the same
  bounds**, with no completeness and no closed graph theorem:
  `‖T⋆y‖² = ‖⟨T(T⋆y), y⟩‖ ≤ C‖T⋆y‖‖y‖`, then cancel.  This is the argument
  that makes the whole theory work without Banach--Steinhaus;
* `opNorm` --- the operator norm as an infimum of bounds, with
  `norm_apply_le_opNorm` (the infimum is attained as a bound),
  `opNorm_le_of_bound`, `opNorm_add_le`, `opNorm_comp_le`, `opNorm_zero`;
* `opNorm_adjoint` --- `‖T⋆‖ = ‖T‖`;
* `opNorm_adjoint_comp_self` --- **the C⋆-identity `‖T⋆T‖ = ‖T‖²`**, which is
  what makes `𝓛(E)` a C⋆-algebra rather than merely a Banach algebra, and
  hence what makes `𝓚(E)` a C⋆-algebra;
* `isBoundedBy_rankOne`, `IsFiniteRank.isBounded` --- the finite-rank ideal
  consists of bounded operators, with the expected constants.

## Why the infimum, and not a supremum

`‖T‖ = sup {‖Tx‖ : ‖x‖ ≤ 1}` needs the supremum to exist, which is
boundedness again, and it needs the unit ball to be nonempty, which fails for
the zero module.  Defining `‖T‖` as the *infimum of the Lipschitz bounds*
makes `opNorm` total --- unbounded operators get `sInf ∅ = 0` --- so
`opNorm_nonneg` is unconditional and every interesting statement carries
`IsBounded` explicitly.  That is the same discipline mathlib uses for
`ContinuousLinearMap.opNorm`.
-/

namespace GroupApproximation
namespace HilbertModule

open OrderZero

universe v w w' w''

variable {B : Type v} [NonUnitalCStarAlgebra B] [PartialOrder B]
  [StarOrderedRing B]

namespace Adjointable

variable {E : CStarModule.{v, w} B} {F : CStarModule.{v, w'} B}
variable {G : CStarModule.{v, w''} B}

/-! ## Differences

Placed here rather than with the other algebraic operations because a
difference of operators is first *needed* here: "`T` is a norm limit of
finite-rank operators" is a statement about `T - S`. -/

/-- The difference of two adjointable operators. -/
def sub (T S : Adjointable E F) : Adjointable E F where
  toFun x := T.toFun x - S.toFun x
  adj y := T.adj y - S.adj y
  inner_adj x y := by
    rw [F.inner_sub_left, T.inner_adj, S.inner_adj, ← E.inner_sub_right]

omit [PartialOrder B] [StarOrderedRing B] in
@[simp] theorem sub_toFun (T S : Adjointable E F) (x : E.carrier) :
    (T.sub S).toFun x = T.toFun x - S.toFun x := rfl

/-- The negative of an adjointable operator. -/
def neg (T : Adjointable E F) : Adjointable E F := (zero E F).sub T

omit [PartialOrder B] [StarOrderedRing B] in
@[simp] theorem neg_toFun (T : Adjointable E F) (x : E.carrier) :
    T.neg.toFun x = -T.toFun x := by
  show (0 : F.carrier) - T.toFun x = -T.toFun x
  rw [zero_sub]

omit [PartialOrder B] [StarOrderedRing B] in
/-- An adjointable map respects differences.  Like `map_add`, this is a
theorem and not an assumption. -/
theorem map_sub (T : Adjointable E F) (x y : E.carrier) :
    T.toFun (x - y) = T.toFun x - T.toFun y := by
  refine F.eq_of_inner_eq fun z => ?_
  rw [T.inner_adj' (x - y) z, E.inner_sub_right, ← T.inner_adj' x z,
    ← T.inner_adj' y z, ← F.inner_sub_right]

omit [PartialOrder B] [StarOrderedRing B] in
/-- The adjoint of an adjointable operator is an involution, as an equality of
operators and not merely of underlying maps: the adjoint field is determined,
and the adjoint relation is a proposition. -/
theorem adjoint_adjoint_eq (T : Adjointable E F) :
    Adjointable.adjoint (Adjointable.adjoint T) = T := rfl

/-! ## Boundedness -/

/-- `T` is bounded by `C`. -/
def IsBoundedBy (T : Adjointable E F) (C : ℝ) : Prop :=
  ∀ x : E.carrier, F.norm (T.toFun x) ≤ C * E.norm x

/-- `T` is bounded. -/
def IsBounded (T : Adjointable E F) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ T.IsBoundedBy C

omit [PartialOrder B] [StarOrderedRing B] in
theorem IsBoundedBy.isBounded {T : Adjointable E F} {C : ℝ} (hC : 0 ≤ C)
    (h : T.IsBoundedBy C) : T.IsBounded := ⟨C, hC, h⟩

omit [PartialOrder B] [StarOrderedRing B] in
theorem IsBoundedBy.mono {T : Adjointable E F} {C D : ℝ} (h : T.IsBoundedBy C)
    (hCD : C ≤ D) : T.IsBoundedBy D := by
  intro x
  exact le_trans (h x) (mul_le_mul_of_nonneg_right hCD (E.norm_nonneg x))

/-- **An operator and its adjoint obey the same bounds.**

The proof is the one line that replaces the closed graph theorem:
`‖T⋆y‖² = ‖⟨T⋆y, T⋆y⟩‖ = ‖⟨T(T⋆y), y⟩‖ ≤ ‖T(T⋆y)‖‖y‖ ≤ C‖T⋆y‖‖y‖`, and one
cancels `‖T⋆y‖`.  Nothing about completeness is used. -/
theorem IsBoundedBy.adjoint {T : Adjointable E F} {C : ℝ} (h : T.IsBoundedBy C)
    (hC : 0 ≤ C) : (Adjointable.adjoint T).IsBoundedBy C := by
  intro y
  show E.norm (T.adj y) ≤ C * F.norm y
  have key : E.norm (T.adj y) ^ 2 ≤ C * F.norm y * E.norm (T.adj y) := by
    have h1 : E.inner (T.adj y) (T.adj y) = F.inner (T.toFun (T.adj y)) y :=
      (T.inner_adj (T.adj y) y).symm
    calc E.norm (T.adj y) ^ 2 = ‖E.inner (T.adj y) (T.adj y)‖ := E.norm_sq _
      _ = ‖F.inner (T.toFun (T.adj y)) y‖ := by rw [h1]
      _ ≤ F.norm (T.toFun (T.adj y)) * F.norm y := F.norm_inner_le _ _
      _ ≤ C * E.norm (T.adj y) * F.norm y :=
          mul_le_mul_of_nonneg_right (h _) (F.norm_nonneg y)
      _ = C * F.norm y * E.norm (T.adj y) := by ring
  rcases eq_or_lt_of_le (E.norm_nonneg (T.adj y)) with hzero | hpos
  · rw [← hzero]
    exact mul_nonneg hC (F.norm_nonneg y)
  · refine le_of_mul_le_mul_right ?_ hpos
    calc E.norm (T.adj y) * E.norm (T.adj y) = E.norm (T.adj y) ^ 2 :=
          (pow_two _).symm
      _ ≤ C * F.norm y * E.norm (T.adj y) := key

theorem IsBounded.adjoint {T : Adjointable E F} (h : T.IsBounded) :
    (Adjointable.adjoint T).IsBounded := by
  obtain ⟨C, hC, hb⟩ := h
  exact ⟨C, hC, hb.adjoint hC⟩

theorem IsBoundedBy.add {T S : Adjointable E F} {C D : ℝ}
    (hT : T.IsBoundedBy C) (hS : S.IsBoundedBy D) :
    (T.add S).IsBoundedBy (C + D) := by
  intro x
  show F.norm (T.toFun x + S.toFun x) ≤ (C + D) * E.norm x
  calc F.norm (T.toFun x + S.toFun x)
      ≤ F.norm (T.toFun x) + F.norm (S.toFun x) := F.norm_add_le _ _
    _ ≤ C * E.norm x + D * E.norm x := add_le_add (hT x) (hS x)
    _ = (C + D) * E.norm x := by ring

theorem IsBoundedBy.sub {T S : Adjointable E F} {C D : ℝ}
    (hT : T.IsBoundedBy C) (hS : S.IsBoundedBy D) :
    (T.sub S).IsBoundedBy (C + D) := by
  intro x
  show F.norm (T.toFun x - S.toFun x) ≤ (C + D) * E.norm x
  have hrw : T.toFun x - S.toFun x = T.toFun x + -S.toFun x := by
    rw [sub_eq_add_neg]
  rw [hrw]
  calc F.norm (T.toFun x + -S.toFun x)
      ≤ F.norm (T.toFun x) + F.norm (-S.toFun x) := F.norm_add_le _ _
    _ = F.norm (T.toFun x) + F.norm (S.toFun x) := by
        rw [F.norm_neg]
    _ ≤ C * E.norm x + D * E.norm x := add_le_add (hT x) (hS x)
    _ = (C + D) * E.norm x := by ring

omit [PartialOrder B] [StarOrderedRing B] in
theorem IsBoundedBy.comp {S : Adjointable F G} {T : Adjointable E F} {C D : ℝ}
    (hS : S.IsBoundedBy C) (hT : T.IsBoundedBy D) (hC : 0 ≤ C) :
    (S.comp T).IsBoundedBy (C * D) := by
  intro x
  show G.norm (S.toFun (T.toFun x)) ≤ C * D * E.norm x
  calc G.norm (S.toFun (T.toFun x)) ≤ C * F.norm (T.toFun x) := hS _
    _ ≤ C * (D * E.norm x) := mul_le_mul_of_nonneg_left (hT x) hC
    _ = C * D * E.norm x := by ring

/-! ## Rank-one and finite-rank operators are bounded -/

theorem isBoundedBy_rankOne (x : F.carrier) (y : E.carrier) :
    (rankOne x y).IsBoundedBy (F.norm x * E.norm y) := by
  intro z
  show F.norm (F.act x (E.inner y z)) ≤ F.norm x * E.norm y * E.norm z
  calc F.norm (F.act x (E.inner y z)) ≤ F.norm x * ‖E.inner y z‖ :=
        F.norm_act_le _ _
    _ ≤ F.norm x * (E.norm y * E.norm z) :=
        mul_le_mul_of_nonneg_left (E.norm_inner_le y z) (F.norm_nonneg x)
    _ = F.norm x * E.norm y * E.norm z := by ring

/-- **A finite-rank operator is bounded**, by the sum of the products of the
norms of its defining vectors. -/
theorem IsFiniteRank.isBounded {T : Adjointable E F} (h : T.IsFiniteRank) :
    T.IsBounded := by
  obtain ⟨ι, hι, x, y, hT⟩ := h
  refine ⟨∑ i, F.norm (x i) * E.norm (y i), ?_, ?_⟩
  · exact Finset.sum_nonneg fun i _ =>
      mul_nonneg (F.norm_nonneg _) (E.norm_nonneg _)
  · intro z
    rw [hT z]
    calc F.norm (∑ i, F.act (x i) (E.inner (y i) z))
        ≤ ∑ i, F.norm (F.act (x i) (E.inner (y i) z)) := F.norm_sum_le _ _
      _ ≤ ∑ i, F.norm (x i) * E.norm (y i) * E.norm z :=
          Finset.sum_le_sum fun i _ => isBoundedBy_rankOne (x i) (y i) z
      _ = (∑ i, F.norm (x i) * E.norm (y i)) * E.norm z := by
          rw [Finset.sum_mul]

/-! ## The operator norm -/

/-- The set of Lipschitz bounds of `T`. -/
def boundSet (T : Adjointable E F) : Set ℝ := {C : ℝ | 0 ≤ C ∧ T.IsBoundedBy C}

omit [PartialOrder B] [StarOrderedRing B] in
theorem bddBelow_boundSet (T : Adjointable E F) : BddBelow T.boundSet :=
  ⟨0, fun _ hC => hC.1⟩

omit [PartialOrder B] [StarOrderedRing B] in
theorem boundSet_nonempty {T : Adjointable E F} (h : T.IsBounded) :
    T.boundSet.Nonempty := by
  obtain ⟨C, hC, hb⟩ := h
  exact ⟨C, hC, hb⟩

/-- **The operator norm**, the infimum of the Lipschitz bounds.  For an
unbounded operator this is `sInf ∅ = 0`, so every statement about it that says
anything carries `IsBounded`. -/
noncomputable def opNorm (T : Adjointable E F) : ℝ := sInf T.boundSet

omit [PartialOrder B] [StarOrderedRing B] in
theorem opNorm_nonneg (T : Adjointable E F) : 0 ≤ T.opNorm := by
  rcases Set.eq_empty_or_nonempty T.boundSet with he | hne
  · rw [opNorm, he]
    exact le_of_eq Real.sInf_empty.symm
  · exact le_csInf hne fun _ hC => hC.1

omit [PartialOrder B] [StarOrderedRing B] in
theorem opNorm_le_of_bound {T : Adjointable E F} {C : ℝ} (hC : 0 ≤ C)
    (h : T.IsBoundedBy C) : T.opNorm ≤ C :=
  csInf_le T.bddBelow_boundSet ⟨hC, h⟩

omit [PartialOrder B] [StarOrderedRing B] in
/-- **The infimum of the bounds is itself a bound.** -/
theorem norm_apply_le_opNorm {T : Adjointable E F} (hT : T.IsBounded)
    (x : E.carrier) : F.norm (T.toFun x) ≤ T.opNorm * E.norm x := by
  rcases eq_or_lt_of_le (E.norm_nonneg x) with hx | hx
  · have hx0 : x = 0 := (E.norm_eq_zero_iff x).mp hx.symm
    have hT0 : T.toFun x = 0 := by rw [hx0, T.map_zero]
    rw [hT0, hx0]
    simp
  · rw [← div_le_iff₀ hx]
    refine le_csInf (boundSet_nonempty hT) ?_
    rintro C ⟨-, hCb⟩
    exact (div_le_iff₀ hx).mpr (hCb x)

omit [PartialOrder B] [StarOrderedRing B] in
theorem isBoundedBy_opNorm {T : Adjointable E F} (hT : T.IsBounded) :
    T.IsBoundedBy T.opNorm :=
  fun x => norm_apply_le_opNorm hT x

omit [PartialOrder B] [StarOrderedRing B] in
@[simp] theorem opNorm_zero : (zero E F).opNorm = 0 := by
  refine le_antisymm (opNorm_le_of_bound le_rfl ?_) (opNorm_nonneg _)
  intro x
  show F.norm (0 : F.carrier) ≤ 0 * E.norm x
  rw [F.norm_zero_vector, zero_mul]

theorem opNorm_add_le {T S : Adjointable E F} (hT : T.IsBounded)
    (hS : S.IsBounded) : (T.add S).opNorm ≤ T.opNorm + S.opNorm :=
  opNorm_le_of_bound (add_nonneg (opNorm_nonneg T) (opNorm_nonneg S))
    ((isBoundedBy_opNorm hT).add (isBoundedBy_opNorm hS))

theorem opNorm_sub_le {T S : Adjointable E F} (hT : T.IsBounded)
    (hS : S.IsBounded) : (T.sub S).opNorm ≤ T.opNorm + S.opNorm :=
  opNorm_le_of_bound (add_nonneg (opNorm_nonneg T) (opNorm_nonneg S))
    ((isBoundedBy_opNorm hT).sub (isBoundedBy_opNorm hS))

omit [PartialOrder B] [StarOrderedRing B] in
theorem opNorm_comp_le {S : Adjointable F G} {T : Adjointable E F}
    (hS : S.IsBounded) (hT : T.IsBounded) :
    (S.comp T).opNorm ≤ S.opNorm * T.opNorm :=
  opNorm_le_of_bound (mul_nonneg (opNorm_nonneg S) (opNorm_nonneg T))
    ((isBoundedBy_opNorm hS).comp (isBoundedBy_opNorm hT) (opNorm_nonneg S))

/-- **The adjoint is isometric.** -/
theorem opNorm_adjoint {T : Adjointable E F} (hT : T.IsBounded) :
    (Adjointable.adjoint T).opNorm = T.opNorm := by
  refine le_antisymm ?_ ?_
  · exact opNorm_le_of_bound (opNorm_nonneg T)
      ((isBoundedBy_opNorm hT).adjoint (opNorm_nonneg T))
  · have h := opNorm_le_of_bound (opNorm_nonneg (Adjointable.adjoint T))
      ((isBoundedBy_opNorm hT.adjoint).adjoint
        (opNorm_nonneg (Adjointable.adjoint T)))
    rwa [adjoint_adjoint_eq] at h

/-! ## The C⋆-identity

`‖T⋆T‖ = ‖T‖²`.  One direction is submultiplicativity together with
`opNorm_adjoint`; the other is the computation
`‖Tx‖² = ‖⟨x, T⋆Tx⟩‖ ≤ ‖x‖‖T⋆Tx‖ ≤ ‖T⋆T‖‖x‖²`, which is where the inner
product does the work that no Banach-algebra argument could. -/

theorem opNorm_sq_le_opNorm_adjoint_comp_self {T : Adjointable E F}
    (hT : T.IsBounded) :
    T.opNorm ^ 2 ≤ ((Adjointable.adjoint T).comp T).opNorm := by
  have hKnonneg : 0 ≤ ((Adjointable.adjoint T).comp T).opNorm :=
    opNorm_nonneg _
  have hcomp : ((Adjointable.adjoint T).comp T).IsBounded :=
    ⟨(Adjointable.adjoint T).opNorm * T.opNorm,
      mul_nonneg (opNorm_nonneg _) (opNorm_nonneg _),
      (isBoundedBy_opNorm hT.adjoint).comp (isBoundedBy_opNorm hT)
        (opNorm_nonneg _)⟩
  have hbound :
      T.IsBoundedBy (Real.sqrt ((Adjointable.adjoint T).comp T).opNorm) := by
    intro x
    have hkey : F.norm (T.toFun x) ^ 2
        ≤ ((Adjointable.adjoint T).comp T).opNorm * E.norm x ^ 2 := by
      calc F.norm (T.toFun x) ^ 2 = ‖F.inner (T.toFun x) (T.toFun x)‖ :=
            F.norm_sq _
        _ = ‖E.inner x (T.adj (T.toFun x))‖ := by rw [T.inner_adj]
        _ ≤ E.norm x * E.norm (T.adj (T.toFun x)) := E.norm_inner_le _ _
        _ ≤ E.norm x * (((Adjointable.adjoint T).comp T).opNorm * E.norm x) :=
            mul_le_mul_of_nonneg_left
              (norm_apply_le_opNorm hcomp x) (E.norm_nonneg x)
        _ = ((Adjointable.adjoint T).comp T).opNorm * E.norm x ^ 2 := by ring
    have hsq : F.norm (T.toFun x) ^ 2
        ≤ (Real.sqrt ((Adjointable.adjoint T).comp T).opNorm * E.norm x) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hKnonneg]
      exact hkey
    refine (pow_le_pow_iff_left₀ (F.norm_nonneg _) ?_
      (by norm_num : (2 : ℕ) ≠ 0)).mp hsq
    exact mul_nonneg (Real.sqrt_nonneg _) (E.norm_nonneg x)
  have hle : T.opNorm ≤ Real.sqrt ((Adjointable.adjoint T).comp T).opNorm :=
    opNorm_le_of_bound (Real.sqrt_nonneg _) hbound
  calc T.opNorm ^ 2
      ≤ Real.sqrt ((Adjointable.adjoint T).comp T).opNorm ^ 2 :=
        pow_le_pow_left₀ (opNorm_nonneg T) hle 2
    _ = ((Adjointable.adjoint T).comp T).opNorm := Real.sq_sqrt hKnonneg

/-- **The C⋆-identity for adjointable operators**: `‖T⋆T‖ = ‖T‖²`.

This is the statement that `𝓛(E)` is a C⋆-algebra and not merely a Banach
`⋆`-algebra, and it is what `𝓚(E)` inherits. -/
theorem opNorm_adjoint_comp_self {T : Adjointable E F} (hT : T.IsBounded) :
    ((Adjointable.adjoint T).comp T).opNorm = T.opNorm ^ 2 := by
  refine le_antisymm ?_ (opNorm_sq_le_opNorm_adjoint_comp_self hT)
  calc ((Adjointable.adjoint T).comp T).opNorm
      ≤ (Adjointable.adjoint T).opNorm * T.opNorm :=
        opNorm_comp_le hT.adjoint hT
    _ = T.opNorm * T.opNorm := by rw [opNorm_adjoint hT]
    _ = T.opNorm ^ 2 := (pow_two _).symm

end Adjointable

end HilbertModule
end GroupApproximation
