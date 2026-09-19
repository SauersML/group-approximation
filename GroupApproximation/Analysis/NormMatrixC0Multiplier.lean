import Mathlib.Analysis.Normed.Operator.Banach
import GroupApproximation.Analysis.CStarAdjointableNorm
import GroupApproximation.Analysis.NormMatrixCorona

/-!
# The bounded product is the multiplier algebra of the matrix `c₀`-sum

For a sequence of nonzero finite matrix algebras, let

`B = ⨁ₙ M_{dₙ}(ℂ)`

be the `c₀`-sum, realized as the closed ideal of operator-norm-null sequences
inside the bounded product.  This file proves the sentence used in the
Introduction of `non_mf_groups_exist.tex`: every multiplier of `B` is left
multiplication by a unique bounded matrix sequence.  Thus

`M(B) = ∏ₙ M_{dₙ}(ℂ)`.

The proof is intrinsic.  Adjointability first gives boundedness by the closed
graph theorem.  The central coordinate projections then recover the unique
bounded sequence coordinate by coordinate, and module-linearity shows that it
acts on every element of the `c₀`-sum by pointwise left multiplication.
-/

namespace GroupApproximation
namespace NormMatrixC0Multiplier

open Filter Matrix
open scoped Matrix.Norms.L2Operator ENNReal

universe u

noncomputable section

variable (X : ℕ → Type u) [∀ n, Fintype (X n)] [∀ n, DecidableEq (X n)]
  [∀ n, Nonempty (X n)]

/-- The bounded product `∏ₙ M_{dₙ}(ℂ)`. -/
abbrev Product := BoundedMatrixSequence X

/-- Assemble the C-star parent already carried coordinatewise by the
dependent `ℓ∞` product. -/
noncomputable local instance productCStarAlgebra : CStarAlgebra (Product X) where
  toNormedRing := inferInstance
  toStarRing := inferInstance
  toCompleteSpace := inferInstance
  toCStarRing := inferInstance
  toNormedAlgebra := inferInstance
  toStarModule := inferInstance

/-- The null-sequence ideal, packaged as a nonunital star subalgebra so its
closed carrier inherits the nonunital C-star structure. -/
def c0StarSubalgebra : NonUnitalStarSubalgebra ℂ (Product X) where
  carrier := nullMatrixSequenceIdeal X cofinite
  zero_mem' := (nullMatrixSequenceIdeal X cofinite).zero_mem
  add_mem' := (nullMatrixSequenceIdeal X cofinite).add_mem
  mul_mem' := fun _ hb ↦
    (nullMatrixSequenceIdeal X cofinite).mul_mem_left _ hb
  smul_mem' := fun c x hx ↦ by
    change IsNullMatrixSequence X cofinite (c • x)
    change IsNullMatrixSequence X cofinite x at hx
    simpa [IsNullMatrixSequence, norm_smul] using
      tendsto_const_nhds.mul hx
  star_mem' := nullMatrixSequenceIdeal_star_mem X cofinite

noncomputable instance c0StarSubalgebra_isClosed :
    IsClosed (c0StarSubalgebra X : Set (Product X)) :=
  inferInstanceAs
    (IsClosed (nullMatrixSequenceIdeal X cofinite : Set (Product X)))

/-- The `c₀`-direct sum `⨁ₙ M_{dₙ}(ℂ)`, as a closed ideal in the product. -/
abbrev C0Sum := ↥(c0StarSubalgebra X)

noncomputable instance c0Sum_nonUnitalCStarAlgebra :
    NonUnitalCStarAlgebra (C0Sum X) :=
  NonUnitalStarSubalgebra.nonUnitalCStarAlgebra (c0StarSubalgebra X)

/-- The identity matrix in coordinate `n`, and zero elsewhere, regarded as an
element of the `c₀`-sum. -/
def coordinateUnit (n : ℕ) : C0Sum X :=
  ⟨lp.single ∞ n (1 : Matrix (X n) (X n) ℂ), by
    change IsNullMatrixSequence X cofinite _
    rw [Nat.cofinite_eq_atTop, IsNullMatrixSequence, Metric.tendsto_atTop]
    intro ε hε
    refine ⟨n + 1, fun m hm ↦ ?_⟩
    have hmn : m ≠ n := Nat.ne_of_gt (lt_of_lt_of_le (Nat.lt_succ_self n) hm)
    rw [Real.dist_eq, sub_zero, abs_norm, lp.single_apply_ne _ _ _ hmn, norm_zero]
    exact hε⟩

@[simp]
theorem coordinateUnit_apply_self (n : ℕ) :
    (coordinateUnit X n : Product X) n = 1 :=
  lp.single_apply_self ∞ n 1

@[simp]
theorem norm_coordinateUnit (n : ℕ) : ‖coordinateUnit X n‖ = 1 := by
  change ‖(lp.single ∞ n (1 : Matrix (X n) (X n) ℂ) : Product X)‖ = 1
  rw [lp.norm_single (by simp)]
  exact norm_one

/-- A bounded matrix sequence acts on the `c₀`-sum by left multiplication.
Its adjoint acts by the pointwise adjoint sequence. -/
def leftMultiplier (a : Product X) : HilbertModule.Multiplier (C0Sum X) where
  toFun x :=
    ⟨a * x.1, IsNullMatrixSequence.mul_left X cofinite a x.2⟩
  adj x :=
    ⟨star a * x.1, IsNullMatrixSequence.mul_left X cofinite (star a) x.2⟩
  inner_adj x y := by
    apply Subtype.ext
    change star (a * x.1) * y.1 = star x.1 * (star a * y.1)
    rw [star_mul, mul_assoc]

@[simp]
theorem leftMultiplier_apply (a : Product X) (x : C0Sum X) :
    (leftMultiplier X a).toFun x =
      ⟨a * x.1, IsNullMatrixSequence.mul_left X cofinite a x.2⟩ :=
  rfl

/-! The algebra operations in the identification.  These are stated on
actions because `HilbertModule.Multiplier` deliberately carries no redundant
algebra typeclasses: its addition, composition and adjoint are the bundled
operations below. -/

@[simp]
theorem leftMultiplier_zero_apply (x : C0Sum X) :
    (leftMultiplier X (0 : Product X)).toFun x =
      (HilbertModule.Adjointable.zero
        (HilbertModule.selfModule (C0Sum X))
        (HilbertModule.selfModule (C0Sum X))).toFun x := by
  apply Subtype.ext
  exact zero_mul x.1

@[simp]
theorem leftMultiplier_one_apply (x : C0Sum X) :
    (leftMultiplier X (1 : Product X)).toFun x =
      (HilbertModule.Adjointable.id
        (HilbertModule.selfModule (C0Sum X))).toFun x := by
  apply Subtype.ext
  exact one_mul x.1

theorem leftMultiplier_add_apply (a b : Product X) (x : C0Sum X) :
    (leftMultiplier X (a + b)).toFun x =
      ((leftMultiplier X a).add (leftMultiplier X b)).toFun x := by
  apply Subtype.ext
  exact add_mul a b x.1

theorem leftMultiplier_mul_apply (a b : Product X) (x : C0Sum X) :
    (leftMultiplier X (a * b)).toFun x =
      ((leftMultiplier X a).comp (leftMultiplier X b)).toFun x := by
  apply Subtype.ext
  exact mul_assoc a b x.1

@[simp]
theorem leftMultiplier_star_apply (a : Product X) (x : C0Sum X) :
    (leftMultiplier X (star a)).toFun x =
      (HilbertModule.Adjointable.adjoint (leftMultiplier X a)).toFun x :=
  rfl

/-- The underlying complex-linear map of a multiplier.  Linearity is a
theorem of adjointability, not extra structure in `Multiplier`. -/
def multiplierLinearMap (T : HilbertModule.Multiplier (C0Sum X)) :
    C0Sum X →ₗ[ℂ] C0Sum X where
  toFun := T.toFun
  map_add' := T.map_add
  map_smul' := T.map_smul

/-- Every adjointable operator on a C-star algebra regarded as a module over
itself is bounded.  Here completeness permits the standard closed-graph
argument that the general bundled Hilbert-module API intentionally does not
assume. -/
theorem multiplier_isBounded (T : HilbertModule.Multiplier (C0Sum X)) :
    T.IsBounded := by
  let g := multiplierLinearMap X T
  have hg : Continuous g := g.continuous_of_seq_closed_graph (by
    intro v x y hv hTv
    apply (HilbertModule.selfModule (C0Sum X)).eq_of_inner_eq
    intro z
    have hleft : Tendsto (fun n ↦ star z * (g (v n))) atTop
        (nhds (star z * y)) := tendsto_const_nhds.mul hTv
    have hright : Tendsto (fun n ↦ star (T.adj z) * v n) atTop
        (nhds (star (T.adj z) * x)) := tendsto_const_nhds.mul hv
    have hterm : ∀ n, star z * g (v n) = star (T.adj z) * v n := by
      intro n
      exact T.inner_adj' (v n) z
    have hright' : Tendsto (fun n ↦ star z * g (v n)) atTop
        (nhds (star (T.adj z) * x)) :=
      hright.congr' (Eventually.of_forall fun n ↦ (hterm n).symm)
    have hlimit : star z * y = star (T.adj z) * x :=
      tendsto_nhds_unique hleft hright'
    exact hlimit.trans (T.inner_adj' x z).symm)
  obtain ⟨C, hC, hbound⟩ := SemilinearMapClass.bound_of_continuous g hg
  refine ⟨C, hC.le, fun x ↦ ?_⟩
  rw [HilbertModule.selfModule_norm, HilbertModule.selfModule_norm]
  exact hbound x

/-- The `n`-th coordinate of the bounded sequence represented by a
multiplier: apply it to the `n`-th central coordinate projection and read the
same coordinate. -/
def symbol (T : HilbertModule.Multiplier (C0Sum X)) (n : ℕ) :
    Matrix (X n) (X n) ℂ :=
  (T.toFun (coordinateUnit X n)).1 n

theorem symbol_norm_le_of_isBoundedBy
    (T : HilbertModule.Multiplier (C0Sum X)) {C : ℝ}
    (hT : T.IsBoundedBy C) (n : ℕ) : ‖symbol X T n‖ ≤ C := by
  calc
    ‖symbol X T n‖ ≤ ‖(T.toFun (coordinateUnit X n)).1‖ :=
      boundedMatrixSequence_coord_norm_le X _ n
    _ = ‖T.toFun (coordinateUnit X n)‖ := rfl
    _ ≤ C * ‖coordinateUnit X n‖ := by
      simpa only [HilbertModule.selfModule_norm] using
        hT (coordinateUnit X n)
    _ = C := by rw [norm_coordinateUnit]; ring

/-- The coordinate symbol of a multiplier is uniformly bounded, hence is an
element of the bounded product. -/
theorem exists_symbol_product (T : HilbertModule.Multiplier (C0Sum X)) :
    ∃ a : Product X, ∀ n, a n = symbol X T n := by
  obtain ⟨C, -, hT⟩ := multiplier_isBounded X T
  refine ⟨⟨fun n ↦ symbol X T n, memℓp_infty ?_⟩, fun _ ↦ rfl⟩
  exact ⟨C, by
    rintro _ ⟨n, rfl⟩
    exact symbol_norm_le_of_isBoundedBy X T hT n⟩

/-- A coordinate projection commutes with every element of the `c₀`-sum. -/
theorem coordinateUnit_commutes (n : ℕ) (x : C0Sum X) :
    coordinateUnit X n * x = x * coordinateUnit X n := by
  apply Subtype.ext
  refine lp.ext (funext fun m ↦ ?_)
  by_cases hmn : m = n
  · subst m
    simp [coordinateUnit]
  · have hzero : (coordinateUnit X n : Product X) m = 0 := by
      exact lp.single_apply_ne
        (E := fun k ↦ Matrix (X k) (X k) ℂ) ∞ n 1 hmn
    change (coordinateUnit X n : Product X) m * x.1 m =
      x.1 m * (coordinateUnit X n : Product X) m
    rw [hzero, zero_mul, mul_zero]

/-- The symbol recovered from `T` acts exactly as `T` on the `c₀`-sum. -/
theorem symbol_mul_apply (T : HilbertModule.Multiplier (C0Sum X))
    (x : C0Sum X) (n : ℕ) :
    symbol X T n * x.1 n = (T.toFun x).1 n := by
  have hleft := T.map_act (coordinateUnit X n) x
  have hright := T.map_act x (coordinateUnit X n)
  have hcomm := coordinateUnit_commutes X n x
  have hoperators : T.toFun (coordinateUnit X n) * x =
      T.toFun x * coordinateUnit X n := by
    calc
      T.toFun (coordinateUnit X n) * x =
          T.toFun (coordinateUnit X n * x) := hleft.symm
      _ = T.toFun (x * coordinateUnit X n) := congrArg T.toFun hcomm
      _ = T.toFun x * coordinateUnit X n := hright
  have hcoord := congrArg (fun y : C0Sum X ↦ y.1 n) hoperators
  simpa [symbol, coordinateUnit] using hcoord

/-- Left multiplication by `a` has operator norm exactly `‖a‖`.  Together
with the algebra-operation formulas above and surjectivity below, this makes
the multiplier identification isometric, not merely a bijection of sets. -/
theorem opNorm_leftMultiplier (a : Product X) :
    HilbertModule.Adjointable.opNorm (leftMultiplier X a) = ‖a‖ := by
  have hbound :
      HilbertModule.Adjointable.IsBoundedBy (leftMultiplier X a) ‖a‖ := by
    intro x
    rw [leftMultiplier_apply]
    simp only [HilbertModule.selfModule_norm]
    exact norm_mul_le a x.1
  have hbounded :
      HilbertModule.Adjointable.IsBounded (leftMultiplier X a) :=
    hbound.isBounded (norm_nonneg a)
  apply le_antisymm
  · exact HilbertModule.Adjointable.opNorm_le_of_bound (norm_nonneg a) hbound
  · rw [boundedMatrixSequence_norm_eq_ciSup]
    refine ciSup_le fun n ↦ ?_
    have hcoord := boundedMatrixSequence_coord_norm_le X
      ((leftMultiplier X a).toFun (coordinateUnit X n)).1 n
    have happ :=
      HilbertModule.Adjointable.norm_apply_le_opNorm hbounded
        (coordinateUnit X n)
    calc
      ‖a n‖ = ‖((leftMultiplier X a).toFun (coordinateUnit X n)).1 n‖ := by
        simp [leftMultiplier, coordinateUnit]
      _ ≤ ‖(leftMultiplier X a).toFun (coordinateUnit X n)‖ := hcoord
      _ ≤ HilbertModule.Adjointable.opNorm (leftMultiplier X a) *
          ‖coordinateUnit X n‖ := by
        simpa only [HilbertModule.selfModule_norm] using happ
      _ = HilbertModule.Adjointable.opNorm (leftMultiplier X a) := by
        rw [norm_coordinateUnit, mul_one]

/-- **The product is the multiplier algebra of the `c₀`-sum.**  Every
multiplier is left multiplication by a unique bounded matrix sequence.  This
is the precise formal content of

`M(⨁ₙ M_{dₙ}(ℂ)) = ∏ₙ M_{dₙ}(ℂ)`.
-/
theorem existsUnique_leftMultiplier
    (T : HilbertModule.Multiplier (C0Sum X)) :
    ∃! a : Product X, ∀ x : C0Sum X,
      (leftMultiplier X a).toFun x = T.toFun x := by
  obtain ⟨a, ha⟩ := exists_symbol_product X T
  have haction : ∀ x : C0Sum X,
      (leftMultiplier X a).toFun x = T.toFun x := by
    intro x
    apply Subtype.ext
    refine lp.ext (funext fun n ↦ ?_)
    change a n * x.1 n = (T.toFun x).1 n
    rw [ha n]
    exact symbol_mul_apply X T x n
  refine ⟨a, haction, ?_⟩
  · intro b hb
    refine lp.ext (funext fun n ↦ ?_)
    have hb_n := congrArg (fun y : C0Sum X ↦ y.1 n)
      (hb (coordinateUnit X n))
    have ha_n := congrArg (fun y : C0Sum X ↦ y.1 n)
      (haction (coordinateUnit X n))
    have hab : b n = a n := by
      simpa [leftMultiplier, coordinateUnit] using hb_n.trans ha_n.symm
    exact hab

end

end NormMatrixC0Multiplier
end GroupApproximation
