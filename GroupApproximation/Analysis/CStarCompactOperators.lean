import GroupApproximation.Analysis.CStarAdjointableNorm

/-!
# The compact operators `𝓚(E)`

A Kasparov `A`-`B`-bimodule is a representation `π : A → 𝓛(E)` together with
`F ∈ 𝓛(E)` for which `(F² - 1)π(a)`, `(F - F⋆)π(a)` and `[F, π(a)]` are
**compact**.  Everything in `KK`-theory is stated modulo `𝓚(E)`, so `𝓚(E)` is
the object the theory is *about*, and until now this development could only
build the finite-rank operators (`Analysis.CStarFiniteRank`) --- the closure
was missing because the norm was missing.  `Analysis.CStarAdjointableNorm`
supplies the norm; this file takes the closure.

## What is proved

`IsCompactOp T` says: `T` is bounded, and for every `ε > 0` there is a
finite-rank `S` with `‖T - S‖ ≤ ε`.  The approximation is phrased with
`IsBoundedBy` rather than with `opNorm` so that no statement below depends on
the infimum being attained.

* `IsFiniteRank.isCompactOp`, `isCompactOp_rankOne` --- the generators;
* `IsCompactOp.add`, `IsCompactOp.sub`, `IsCompactOp.smul` --- a linear
  subspace;
* `IsCompactOp.comp_left`, `IsCompactOp.comp_right` --- **a two-sided ideal in
  the bounded adjointable operators**, which is the property `KK`-theory
  consumes: `π(a)·K` and `K·π(a)` are compact for every representation;
* `IsCompactOp.adjoint` --- `⋆`-closed.  Here the algebra is *exact*:
  `(T - S)⋆ = T⋆ - S⋆` holds definitionally for these structures, and
  `IsBoundedBy.adjoint` transports the estimate with the same constant;
* `isCompactOp_of_approx` --- **`𝓚(E)` is closed**: an operator approximable
  by compacts is compact.  This is the `ε/2` argument, and it is what makes
  `𝓚(E)` a C⋆-algebra rather than a dense `⋆`-subalgebra.

Together with `opNorm_adjoint_comp_self` --- the C⋆-identity, proved in the
previous file --- these say exactly that `𝓚(E)` is a closed `⋆`-closed
two-sided ideal in the C⋆-algebra `𝓛(E)`.  That is the statement
`Analysis.KirchbergRordamOrderZeroLift` had to gesture at with an ambient
algebra, and it is the setting in which `𝓛(E) = M(𝓚(E))` is proved.

## Two small algebraic gaps closed on the way

`act_zero_left` and `act_neg_left` --- the action of `B` respects `0` and
negation.  Neither is an axiom of `CStarModule` (the axioms give only
additivity), both follow from it, and `IsFiniteRank.sub` needs them: the
difference of two finite-rank operators is the sum over `ι ⊕ κ` with the
second family's *vectors* negated.

## The one place a division appears

`comp_left` and `comp_right` approximate to `ε/(C+1)` where `C` is a bound for
the *other* factor.  The `+1` is not laziness --- `C` may be `0`, and dividing
by a bound rather than by `‖R‖` avoids needing `opNorm` to be positive, hence
avoids a case split on `R = 0` in every application.
-/

namespace GroupApproximation
namespace HilbertModule

open OrderZero

universe v w w' w''

variable {B : Type v} [NonUnitalCStarAlgebra B] [PartialOrder B]
  [StarOrderedRing B]

namespace CStarModule

variable (E : CStarModule.{v, w} B)

/-- The action of `B` kills `0`. -/
theorem act_zero_left (b : B) : E.act (0 : E.carrier) b = 0 := by
  have h := E.act_add_left 0 0 b
  rw [add_zero] at h
  exact left_eq_add.mp h

/-- The action of `B` respects negation. -/
theorem act_neg_left (x : E.carrier) (b : B) :
    E.act (-x) b = -(E.act x b) := by
  have h := E.act_add_left x (-x) b
  rw [add_neg_cancel, E.act_zero_left] at h
  calc E.act (-x) b = -(E.act x b) + (E.act x b + E.act (-x) b) := by abel
    _ = -(E.act x b) := by rw [← h, add_zero]

end CStarModule

namespace Adjointable

variable {E : CStarModule.{v, w} B} {F : CStarModule.{v, w'} B}
variable {G : CStarModule.{v, w''} B}

/-! ## Scalar multiples

The last operation missing from the `⋆`-algebra structure.  The adjoint of
`c·T` is `c̄·T⋆`, because the inner product is conjugate-linear in its first
variable. -/

/-- The scalar multiple of an adjointable operator. -/
def smul (c : ℂ) (T : Adjointable E F) : Adjointable E F where
  toFun x := c • T.toFun x
  adj y := (starRingEnd ℂ) c • T.adj y
  inner_adj x y := by
    rw [F.inner_smul_left, T.inner_adj, E.inner_smul_right]

@[simp] theorem smul_toFun (c : ℂ) (T : Adjointable E F) (x : E.carrier) :
    (smul c T).toFun x = c • T.toFun x := rfl

theorem IsBoundedBy.smul {T : Adjointable E F} {C : ℝ} (h : T.IsBoundedBy C)
    (c : ℂ) : (Adjointable.smul c T).IsBoundedBy (‖c‖ * C) := by
  intro x
  show F.norm (c • T.toFun x) ≤ ‖c‖ * C * E.norm x
  calc F.norm (c • T.toFun x) = ‖c‖ * F.norm (T.toFun x) := F.norm_smul c _
    _ ≤ ‖c‖ * (C * E.norm x) :=
        mul_le_mul_of_nonneg_left (h x) (norm_nonneg c)
    _ = ‖c‖ * C * E.norm x := by ring

/-- A scalar multiple of a finite-rank operator has finite rank: scale the
first vector of each rank-one summand. -/
theorem IsFiniteRank.smul {T : Adjointable E F} (h : T.IsFiniteRank) (c : ℂ) :
    (Adjointable.smul c T).IsFiniteRank := by
  obtain ⟨ι, hι, x, y, hT⟩ := h
  refine ⟨ι, hι, fun i => c • x i, y, ?_⟩
  intro z
  show c • T.toFun z = ∑ i, F.act (c • x i) (E.inner (y i) z)
  rw [hT z, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [F.act_smul]

/-- The difference of two finite-rank operators has finite rank: the sum over
`ι ⊕ κ` with the second family's vectors negated. -/
theorem IsFiniteRank.sub {T S : Adjointable E F} (hT : T.IsFiniteRank)
    (hS : S.IsFiniteRank) : (T.sub S).IsFiniteRank := by
  obtain ⟨ι, hι, x, y, hTeq⟩ := hT
  obtain ⟨κ, hκ, u, v, hSeq⟩ := hS
  refine ⟨ι ⊕ κ, inferInstance, Sum.elim x (fun b => -u b), Sum.elim y v, ?_⟩
  intro z
  have hsum :
      (∑ i : ι ⊕ κ, F.act (Sum.elim x (fun b => -u b) i)
          (E.inner (Sum.elim y v i) z))
        = (∑ a : ι, F.act (x a) (E.inner (y a) z))
          + ∑ b : κ, F.act (-u b) (E.inner (v b) z) :=
    Fintype.sum_sum_type _
  have hneg : (∑ b : κ, F.act (-u b) (E.inner (v b) z))
      = -∑ b : κ, F.act (u b) (E.inner (v b) z) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [F.act_neg_left]
  show T.toFun z - S.toFun z = _
  rw [hTeq z, hSeq z, hsum, hneg, ← sub_eq_add_neg]

/-! ## Compact operators -/

/-- **`T` is compact**: bounded, and approximable in operator norm by
finite-rank operators. -/
def IsCompactOp (T : Adjointable E F) : Prop :=
  T.IsBounded ∧ ∀ ε : ℝ, 0 < ε → ∃ S : Adjointable E F,
    S.IsFiniteRank ∧ (T.sub S).IsBoundedBy ε

theorem IsCompactOp.isBounded {T : Adjointable E F} (h : T.IsCompactOp) :
    T.IsBounded := h.1

/-- Finite-rank operators are compact: approximate `T` by itself. -/
theorem IsFiniteRank.isCompactOp {T : Adjointable E F} (h : T.IsFiniteRank) :
    T.IsCompactOp := by
  refine ⟨h.isBounded, fun ε hε => ⟨T, h, ?_⟩⟩
  intro x
  show F.norm (T.toFun x - T.toFun x) ≤ ε * E.norm x
  rw [sub_self, F.norm_zero_vector]
  exact mul_nonneg hε.le (E.norm_nonneg x)

theorem isCompactOp_rankOne (x : F.carrier) (y : E.carrier) :
    (rankOne x y).IsCompactOp :=
  (isFiniteRank_rankOne x y).isCompactOp

theorem IsCompactOp.add {T S : Adjointable E F} (hT : T.IsCompactOp)
    (hS : S.IsCompactOp) : (T.add S).IsCompactOp := by
  refine ⟨?_, ?_⟩
  · obtain ⟨C, hC0, hCb⟩ := hT.1
    obtain ⟨D, hD0, hDb⟩ := hS.1
    exact ⟨C + D, add_nonneg hC0 hD0, hCb.add hDb⟩
  · intro ε hε
    obtain ⟨P, hP, hPb⟩ := hT.2 (ε / 2) (half_pos hε)
    obtain ⟨Q, hQ, hQb⟩ := hS.2 (ε / 2) (half_pos hε)
    refine ⟨P.add Q, hP.add hQ, ?_⟩
    intro x
    show F.norm (T.toFun x + S.toFun x - (P.toFun x + Q.toFun x))
      ≤ ε * E.norm x
    have hrw : T.toFun x + S.toFun x - (P.toFun x + Q.toFun x)
        = (T.toFun x - P.toFun x) + (S.toFun x - Q.toFun x) := by abel
    rw [hrw]
    calc F.norm ((T.toFun x - P.toFun x) + (S.toFun x - Q.toFun x))
        ≤ F.norm (T.toFun x - P.toFun x) + F.norm (S.toFun x - Q.toFun x) :=
          F.norm_add_le _ _
      _ ≤ ε / 2 * E.norm x + ε / 2 * E.norm x := add_le_add (hPb x) (hQb x)
      _ = ε * E.norm x := by ring

theorem IsCompactOp.smul {T : Adjointable E F} (h : T.IsCompactOp) (c : ℂ) :
    (Adjointable.smul c T).IsCompactOp := by
  have hcpos : (0 : ℝ) < ‖c‖ + 1 := by positivity
  refine ⟨?_, ?_⟩
  · obtain ⟨C, hC0, hCb⟩ := h.1
    exact ⟨‖c‖ * C, mul_nonneg (norm_nonneg c) hC0, hCb.smul c⟩
  · intro ε hε
    obtain ⟨S, hS, hb⟩ := h.2 (ε / (‖c‖ + 1)) (div_pos hε hcpos)
    refine ⟨Adjointable.smul c S, hS.smul c, ?_⟩
    intro x
    show F.norm (c • T.toFun x - c • S.toFun x) ≤ ε * E.norm x
    have hrw : c • T.toFun x - c • S.toFun x
        = c • (T.toFun x - S.toFun x) := by rw [smul_sub]
    have hcε : ‖c‖ * (ε / (‖c‖ + 1)) ≤ ε := by
      rw [← mul_div_assoc, div_le_iff₀ hcpos]
      nlinarith [hε.le, norm_nonneg c]
    rw [hrw]
    calc F.norm (c • (T.toFun x - S.toFun x))
        = ‖c‖ * F.norm (T.toFun x - S.toFun x) := F.norm_smul c _
      _ ≤ ‖c‖ * (ε / (‖c‖ + 1) * E.norm x) :=
          mul_le_mul_of_nonneg_left (hb x) (norm_nonneg c)
      _ = ‖c‖ * (ε / (‖c‖ + 1)) * E.norm x := by ring
      _ ≤ ε * E.norm x :=
          mul_le_mul_of_nonneg_right hcε (E.norm_nonneg x)

/-- **Left ideal property**: a bounded operator times a compact one is
compact. -/
theorem IsCompactOp.comp_left {T : Adjointable E F} (hT : T.IsCompactOp)
    {R : Adjointable F G} (hR : R.IsBounded) : (R.comp T).IsCompactOp := by
  obtain ⟨C, hC0, hCb⟩ := hR
  have hCpos : (0 : ℝ) < C + 1 := by linarith
  refine ⟨?_, ?_⟩
  · obtain ⟨D, hD0, hDb⟩ := hT.1
    exact ⟨C * D, mul_nonneg hC0 hD0, hCb.comp hDb hC0⟩
  · intro ε hε
    obtain ⟨S, hS, hb⟩ := hT.2 (ε / (C + 1)) (div_pos hε hCpos)
    refine ⟨R.comp S, hS.comp_left R, ?_⟩
    intro x
    show G.norm (R.toFun (T.toFun x) - R.toFun (S.toFun x)) ≤ ε * E.norm x
    have hms : R.toFun (T.toFun x) - R.toFun (S.toFun x)
        = R.toFun (T.toFun x - S.toFun x) := (R.map_sub _ _).symm
    have hCε : C * (ε / (C + 1)) ≤ ε := by
      rw [← mul_div_assoc, div_le_iff₀ hCpos]
      nlinarith [hε.le, hC0]
    rw [hms]
    calc G.norm (R.toFun (T.toFun x - S.toFun x))
        ≤ C * F.norm (T.toFun x - S.toFun x) := hCb _
      _ ≤ C * (ε / (C + 1) * E.norm x) :=
          mul_le_mul_of_nonneg_left (hb x) hC0
      _ = C * (ε / (C + 1)) * E.norm x := by ring
      _ ≤ ε * E.norm x := mul_le_mul_of_nonneg_right hCε (E.norm_nonneg x)

/-- **Right ideal property**: a compact operator times a bounded one is
compact. -/
theorem IsCompactOp.comp_right {T : Adjointable E F} (hT : T.IsCompactOp)
    {R : Adjointable G E} (hR : R.IsBounded) : (T.comp R).IsCompactOp := by
  obtain ⟨C, hC0, hCb⟩ := hR
  have hCpos : (0 : ℝ) < C + 1 := by linarith
  refine ⟨?_, ?_⟩
  · obtain ⟨D, hD0, hDb⟩ := hT.1
    exact ⟨D * C, mul_nonneg hD0 hC0, hDb.comp hCb hD0⟩
  · intro ε hε
    have hεC : (0 : ℝ) ≤ ε / (C + 1) := (div_pos hε hCpos).le
    obtain ⟨S, hS, hb⟩ := hT.2 (ε / (C + 1)) (div_pos hε hCpos)
    refine ⟨S.comp R, hS.comp_right R, ?_⟩
    intro z
    show F.norm (T.toFun (R.toFun z) - S.toFun (R.toFun z)) ≤ ε * G.norm z
    have hCε : ε / (C + 1) * C ≤ ε := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hCpos]
      nlinarith [hε.le, hC0]
    calc F.norm (T.toFun (R.toFun z) - S.toFun (R.toFun z))
        ≤ ε / (C + 1) * E.norm (R.toFun z) := hb _
      _ ≤ ε / (C + 1) * (C * G.norm z) :=
          mul_le_mul_of_nonneg_left (hCb z) hεC
      _ = ε / (C + 1) * C * G.norm z := by ring
      _ ≤ ε * G.norm z := mul_le_mul_of_nonneg_right hCε (G.norm_nonneg z)

/-- **`𝓚(E)` is `⋆`-closed.**

`(T - S)⋆ = T⋆ - S⋆` holds *definitionally* for these structures --- the
adjoint of a difference is the difference of the adjoints by construction ---
so the only content is `IsBoundedBy.adjoint`, which transports the estimate
with the same constant. -/
theorem IsCompactOp.adjoint {T : Adjointable E F} (h : T.IsCompactOp) :
    (Adjointable.adjoint T).IsCompactOp := by
  refine ⟨h.1.adjoint, ?_⟩
  intro ε hε
  obtain ⟨S, hS, hb⟩ := h.2 ε hε
  refine ⟨Adjointable.adjoint S, hS.adjoint, ?_⟩
  have hrfl : (Adjointable.adjoint T).sub (Adjointable.adjoint S)
      = Adjointable.adjoint (T.sub S) := rfl
  rw [hrfl]
  exact hb.adjoint hε.le

/-- The difference of two compact operators is compact. -/
theorem IsCompactOp.sub {T S : Adjointable E F} (hT : T.IsCompactOp)
    (hS : S.IsCompactOp) : (T.sub S).IsCompactOp := by
  refine ⟨?_, ?_⟩
  · obtain ⟨C, hC0, hCb⟩ := hT.1
    obtain ⟨D, hD0, hDb⟩ := hS.1
    exact ⟨C + D, add_nonneg hC0 hD0, hCb.sub hDb⟩
  · intro ε hε
    obtain ⟨P, hP, hPb⟩ := hT.2 (ε / 2) (half_pos hε)
    obtain ⟨Q, hQ, hQb⟩ := hS.2 (ε / 2) (half_pos hε)
    refine ⟨P.sub Q, hP.sub hQ, ?_⟩
    intro x
    show F.norm (T.toFun x - S.toFun x - (P.toFun x - Q.toFun x))
      ≤ ε * E.norm x
    have hrw : T.toFun x - S.toFun x - (P.toFun x - Q.toFun x)
        = (T.toFun x - P.toFun x) - (S.toFun x - Q.toFun x) := by abel
    have hsub : (T.toFun x - P.toFun x) - (S.toFun x - Q.toFun x)
        = (T.toFun x - P.toFun x) + -(S.toFun x - Q.toFun x) :=
      sub_eq_add_neg _ _
    rw [hrw, hsub]
    calc F.norm ((T.toFun x - P.toFun x) + -(S.toFun x - Q.toFun x))
        ≤ F.norm (T.toFun x - P.toFun x)
            + F.norm (-(S.toFun x - Q.toFun x)) := F.norm_add_le _ _
      _ = F.norm (T.toFun x - P.toFun x)
            + F.norm (S.toFun x - Q.toFun x) := by rw [F.norm_neg]
      _ ≤ ε / 2 * E.norm x + ε / 2 * E.norm x := add_le_add (hPb x) (hQb x)
      _ = ε * E.norm x := by ring

/-! ## Pointwise invariance

`IsBoundedBy`, `IsBounded`, `IsFiniteRank` and `IsCompactOp` are statements
about `T.toFun` alone, so two adjointable operators with the same underlying
map satisfy the same ones.  This is what replaces an extensionality principle
for `Adjointable`: an operator identity that holds pointwise transports every
property below without any argument about the adjoint field. -/

theorem IsBoundedBy.congr {T T' : Adjointable E F} {C : ℝ}
    (h : ∀ x, T.toFun x = T'.toFun x) (hT : T.IsBoundedBy C) :
    T'.IsBoundedBy C := by
  intro x
  rw [← h x]
  exact hT x

theorem IsBounded.congr {T T' : Adjointable E F}
    (h : ∀ x, T.toFun x = T'.toFun x) (hT : T.IsBounded) : T'.IsBounded := by
  obtain ⟨C, hC, hb⟩ := hT
  exact ⟨C, hC, hb.congr h⟩

theorem IsFiniteRank.congr {T T' : Adjointable E F}
    (h : ∀ x, T.toFun x = T'.toFun x) (hT : T.IsFiniteRank) :
    T'.IsFiniteRank := by
  obtain ⟨ι, hι, x, y, hTeq⟩ := hT
  refine ⟨ι, hι, x, y, fun z => ?_⟩
  rw [← h z]
  exact hTeq z

theorem IsCompactOp.congr {T T' : Adjointable E F}
    (h : ∀ x, T.toFun x = T'.toFun x) (hT : T.IsCompactOp) :
    T'.IsCompactOp := by
  refine ⟨hT.1.congr h, ?_⟩
  intro ε hε
  obtain ⟨S, hS, hb⟩ := hT.2 ε hε
  refine ⟨S, hS, ?_⟩
  intro x
  show F.norm (T'.toFun x - S.toFun x) ≤ ε * E.norm x
  rw [← h x]
  exact hb x

/-- **`𝓚(E)` is closed in the operator norm.**

If `T` is bounded and approximable by *compact* operators then it is
approximable by finite-rank operators, by the `ε/2` argument.  This is what
makes `𝓚(E)` a C⋆-algebra. -/
theorem isCompactOp_of_approx {T : Adjointable E F} (hT : T.IsBounded)
    (h : ∀ ε : ℝ, 0 < ε → ∃ K : Adjointable E F,
      K.IsCompactOp ∧ (T.sub K).IsBoundedBy ε) : T.IsCompactOp := by
  refine ⟨hT, ?_⟩
  intro ε hε
  obtain ⟨K, hK, hKb⟩ := h (ε / 2) (half_pos hε)
  obtain ⟨S, hS, hSb⟩ := hK.2 (ε / 2) (half_pos hε)
  refine ⟨S, hS, ?_⟩
  intro x
  show F.norm (T.toFun x - S.toFun x) ≤ ε * E.norm x
  have hrw : T.toFun x - S.toFun x
      = (T.toFun x - K.toFun x) + (K.toFun x - S.toFun x) := by abel
  rw [hrw]
  calc F.norm ((T.toFun x - K.toFun x) + (K.toFun x - S.toFun x))
      ≤ F.norm (T.toFun x - K.toFun x) + F.norm (K.toFun x - S.toFun x) :=
        F.norm_add_le _ _
    _ ≤ ε / 2 * E.norm x + ε / 2 * E.norm x := add_le_add (hKb x) (hSb x)
    _ = ε * E.norm x := by ring

end Adjointable

end HilbertModule
end GroupApproximation
