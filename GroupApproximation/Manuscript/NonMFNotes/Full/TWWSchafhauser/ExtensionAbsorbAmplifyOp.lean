import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ExtensionAbsorbAmplifyPos
import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ObstructionSplitExtRing

/-!
# The amplification `T ↦ T ⊗ 1` on `H_J`

Lane `TWWSch3c2A`, work order `WO-TWWSch-3c2-A` (Kasparov 1980, §2; Blackadar §13.6).

Write `H_J = ℓ²(ℕ, J)` and split the index set as `ℕ ≃ ℕ × ℕ` (`Nat.pairEquiv`), so that a
vector `f` of `H_J` is the family of its *columns* `ampCol k f = (f (k, i))ᵢ`, each again a
vector of `H_J`, and `⟨f, g⟩ = ∑ₖ ⟨fₖ, gₖ⟩` (`inner_eq_tsum_ampCol`).  The amplification of an
operator `T` acts on every column: `(T ⊗ 1) f = (T fₖ)ₖ` (`ampVec`, `ampOp`).

The only analytic point is that `(T fₖ)ₖ` is square summable again.  This needs the
*module* bound `⟨Tx, Tx⟩ ≤ C² ⟨x, x⟩` (`IsInnerBoundedBy`), which bounds the row sums, and
the Tonelli-type statement `summable_prod_of_nonneg` for positive families in `J`.  The
passage from a norm bound to a module bound (Paschke's inequality) is used only in
`ExtensionAbsorbAmplify`; here `IsInnerBoundedBy` is an intrinsic property of `T`.

* `inner_eq_tsum_ampCol`: `⟨f, g⟩ = ∑ₖ ⟨fₖ, gₖ⟩`;
* `ampCol_ampVec`: `(T ⊗ 1) f` has columns `T fₖ`;
* `ampOp`: the adjointable operator `T ⊗ 1`, with adjoint `T⋆ ⊗ 1`;
* `isInnerBoundedBy_ampOp`, `isBoundedBy_of_isInnerBoundedBy`: `T ⊗ 1` keeps the bound.
-/

namespace GroupApproximation.Full.TWWSchafhauser

open GroupApproximation.HilbertModule

noncomputable section

section AmplifyOp

variable {J : Type} [NonUnitalCStarAlgebra J] [PartialOrder J] [StarOrderedRing J]

/-- **The module bound** `⟨Tx, Tx⟩ ≤ C² ⟨x, x⟩` for an operator on `H_J`. -/
def IsInnerBoundedBy (T : StdOp J) (C : ℝ) : Prop :=
  ∀ x : (standardModule ℕ J).carrier,
    (standardModule ℕ J).inner (T.toFun x) (T.toFun x)
      ≤ ((C ^ 2 : ℝ) : ℂ) • (standardModule ℕ J).inner x x

/-! ## Columns -/

/-- The square-summable family `p ↦ f(p)⋆ f(p)` pulled back to `ℕ × ℕ`. -/
theorem summable_pair_star_mul (f g : (standardModule ℕ J).carrier) :
    Summable fun p : ℕ × ℕ => star (f.1 (Nat.pairEquiv p)) * g.1 (Nat.pairEquiv p) := by
  have hf : Summable fun n => star (f.1 n) * f.1 n := f.2
  have hg : Summable fun n => star (g.1 n) * g.1 n := g.2
  have h : Summable fun n => star (f.1 n) * g.1 n := summable_star_mul hf hg
  exact (Equiv.summable_iff Nat.pairEquiv).mpr h

/-- **The `k`-th column** `(f (k, i))ᵢ` of a vector of `H_J`. -/
def ampCol (k : ℕ) (f : (standardModule ℕ J).carrier) : (standardModule ℕ J).carrier :=
  ⟨fun i => f.1 (Nat.pairEquiv (k, i)), by
    have h : Summable fun i => star (f.1 (Nat.pairEquiv (k, i))) * f.1 (Nat.pairEquiv (k, i)) :=
      (summable_pair_star_mul f f).prod_factor k
    exact h⟩

theorem ampCol_apply (k : ℕ) (f : (standardModule ℕ J).carrier) (i : ℕ) :
    (ampCol k f).1 i = f.1 (Nat.pairEquiv (k, i)) := rfl

/-- **The inner product is the sum of the inner products of the columns.** -/
theorem inner_eq_tsum_ampCol (f g : (standardModule ℕ J).carrier) :
    (standardModule ℕ J).inner f g
      = ∑' k, (standardModule ℕ J).inner (ampCol k f) (ampCol k g) := by
  show (∑' n, star (f.1 n) * g.1 n)
      = ∑' k, ∑' i, star (f.1 (Nat.pairEquiv (k, i))) * g.1 (Nat.pairEquiv (k, i))
  rw [← Equiv.tsum_eq Nat.pairEquiv fun n => star (f.1 n) * g.1 n]
  exact (summable_pair_star_mul f g).tsum_prod

/-- The inner squares of the columns are summable. -/
theorem summable_inner_ampCol (f : (standardModule ℕ J).carrier) :
    Summable fun k => (standardModule ℕ J).inner (ampCol k f) (ampCol k f) := by
  have h : Summable fun k =>
      ∑' i, star (f.1 (Nat.pairEquiv (k, i))) * f.1 (Nat.pairEquiv (k, i)) :=
    (summable_pair_star_mul f f).prod
  exact h

/-- Under a module bound, the inner squares of the images of the columns are summable. -/
theorem summable_inner_toFun_ampCol {T : StdOp J} {C : ℝ} (hT : IsInnerBoundedBy T C)
    (f : (standardModule ℕ J).carrier) :
    Summable fun k =>
      (standardModule ℕ J).inner (T.toFun (ampCol k f)) (T.toFun (ampCol k f)) :=
  summable_of_nonneg_of_le (fun k => CStarModule.inner_self_nonneg (T.toFun (ampCol k f)))
    (fun k => hT (ampCol k f)) ((summable_inner_ampCol f).const_smul ((C ^ 2 : ℝ) : ℂ))

/-! ## The amplified vector -/

/-- The entries of `(T ⊗ 1) f`, indexed by `ℕ × ℕ`, are square summable. -/
theorem summable_amp_star_mul {T : StdOp J} {C : ℝ} (hT : IsInnerBoundedBy T C)
    (f : (standardModule ℕ J).carrier) :
    Summable fun p : ℕ × ℕ =>
      star ((T.toFun (ampCol p.1 f)).1 p.2) * (T.toFun (ampCol p.1 f)).1 p.2 := by
  refine summable_prod_of_nonneg (fun p => star_mul_self_nonneg _)
    (fun k => by
      have hk : Summable fun i =>
          star ((T.toFun (ampCol k f)).1 i) * (T.toFun (ampCol k f)).1 i :=
        (T.toFun (ampCol k f)).2
      exact hk) ?_
  have h := summable_inner_toFun_ampCol hT f
  exact h

/-- **The amplified vector** `(T ⊗ 1) f = (T fₖ)ₖ`. -/
def ampVec (T : StdOp J) {C : ℝ} (hT : IsInnerBoundedBy T C)
    (f : (standardModule ℕ J).carrier) : (standardModule ℕ J).carrier :=
  ⟨fun n => (T.toFun (ampCol (Nat.pairEquiv.symm n).1 f)).1 (Nat.pairEquiv.symm n).2, by
    exact (Equiv.summable_iff Nat.pairEquiv.symm).mpr (summable_amp_star_mul hT f)⟩

theorem ampVec_apply (T : StdOp J) {C : ℝ} (hT : IsInnerBoundedBy T C)
    (f : (standardModule ℕ J).carrier) (n : ℕ) :
    (ampVec T hT f).1 n
      = (T.toFun (ampCol (Nat.pairEquiv.symm n).1 f)).1 (Nat.pairEquiv.symm n).2 := rfl

/-- **The columns of `(T ⊗ 1) f` are the `T fₖ`.** -/
theorem ampCol_ampVec (T : StdOp J) {C : ℝ} (hT : IsInnerBoundedBy T C)
    (f : (standardModule ℕ J).carrier) (k : ℕ) :
    ampCol k (ampVec T hT f) = T.toFun (ampCol k f) := by
  refine Subtype.ext (funext fun i => ?_)
  exact congrArg (fun p : ℕ × ℕ => (T.toFun (ampCol p.1 f)).1 p.2)
    (Nat.pairEquiv.symm_apply_apply (k, i))

/-- A vector is determined by its columns. -/
theorem ext_ampCol {f g : (standardModule ℕ J).carrier}
    (h : ∀ k, ampCol k f = ampCol k g) : f = g := by
  refine Subtype.ext (funext fun n => ?_)
  have hn := congrArg (fun v : (standardModule ℕ J).carrier => v.1 (Nat.pairEquiv.symm n).2)
    (h (Nat.pairEquiv.symm n).1)
  have he : Nat.pairEquiv ((Nat.pairEquiv.symm n).1, (Nat.pairEquiv.symm n).2) = n :=
    Nat.pairEquiv.apply_symm_apply n
  have hf : f.1 n = (ampCol (Nat.pairEquiv.symm n).1 f).1 (Nat.pairEquiv.symm n).2 :=
    (congrArg f.1 he).symm
  have hg : g.1 n = (ampCol (Nat.pairEquiv.symm n).1 g).1 (Nat.pairEquiv.symm n).2 :=
    (congrArg g.1 he).symm
  exact hf.trans (hn.trans hg.symm)

/-! ## The amplified operator -/

/-- **The amplification** `T ⊗ 1` of an operator with module bounds on `T` and `T⋆`. -/
def ampOp (T : StdOp J) {C : ℝ} (hT : IsInnerBoundedBy T C)
    (hT' : IsInnerBoundedBy (star T) C) : StdOp J where
  toFun := ampVec T hT
  adj := ampVec (star T) hT'
  inner_adj f g := by
    refine (inner_eq_tsum_ampCol (ampVec T hT f) g).trans
      ((tsum_congr fun k => ?_).trans (inner_eq_tsum_ampCol f (ampVec (star T) hT' g)).symm)
    rw [ampCol_ampVec, ampCol_ampVec]
    exact T.inner_adj (ampCol k f) (ampCol k g)

theorem ampOp_toFun (T : StdOp J) {C : ℝ} (hT : IsInnerBoundedBy T C)
    (hT' : IsInnerBoundedBy (star T) C) (f : (standardModule ℕ J).carrier) :
    (ampOp T hT hT').toFun f = ampVec T hT f := rfl

/-- The columns of `(T ⊗ 1) f` are the `T fₖ`, in operator form. -/
theorem ampCol_ampOp (T : StdOp J) {C : ℝ} (hT : IsInnerBoundedBy T C)
    (hT' : IsInnerBoundedBy (star T) C) (f : (standardModule ℕ J).carrier) (k : ℕ) :
    ampCol k ((ampOp T hT hT').toFun f) = T.toFun (ampCol k f) :=
  ampCol_ampVec T hT f k

/-! ## Bounds -/

/-- **`T ⊗ 1` satisfies the module bound of `T`.** -/
theorem isInnerBoundedBy_ampOp (T : StdOp J) {C : ℝ} (hT : IsInnerBoundedBy T C)
    (hT' : IsInnerBoundedBy (star T) C) : IsInnerBoundedBy (ampOp T hT hT') C := by
  intro f
  calc (standardModule ℕ J).inner ((ampOp T hT hT').toFun f) ((ampOp T hT hT').toFun f)
      = ∑' k, (standardModule ℕ J).inner (T.toFun (ampCol k f)) (T.toFun (ampCol k f)) := by
        rw [inner_eq_tsum_ampCol]
        exact tsum_congr fun k => by rw [ampCol_ampOp]
    _ ≤ ∑' k, ((C ^ 2 : ℝ) : ℂ) • (standardModule ℕ J).inner (ampCol k f) (ampCol k f) :=
        Summable.tsum_le_tsum (fun k => hT (ampCol k f)) (summable_inner_toFun_ampCol hT f)
          ((summable_inner_ampCol f).const_smul ((C ^ 2 : ℝ) : ℂ))
    _ = ((C ^ 2 : ℝ) : ℂ) • (standardModule ℕ J).inner f f := by
        rw [(summable_inner_ampCol f).tsum_const_smul ((C ^ 2 : ℝ) : ℂ),
          ← inner_eq_tsum_ampCol]

/-- **A module bound gives a norm bound.** -/
theorem isBoundedBy_of_isInnerBoundedBy {T : StdOp J} {C : ℝ} (hT : IsInnerBoundedBy T C) :
    T.IsBoundedBy |C| := by
  intro x
  have hle : ‖(standardModule ℕ J).inner (T.toFun x) (T.toFun x)‖
      ≤ C ^ 2 * ‖(standardModule ℕ J).inner x x‖ := by
    refine (OrderZero.norm_le_norm_of_nonneg_of_le
      (CStarModule.inner_self_nonneg (T.toFun x)) (hT x)).trans_eq ?_
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg C)]
  rw [CStarModule.norm_def, CStarModule.norm_def, ← Real.sqrt_sq_eq_abs,
    ← Real.sqrt_mul (sq_nonneg C)]
  exact Real.sqrt_le_sqrt hle

/-- A module bound makes the operator bounded. -/
theorem isBounded_of_isInnerBoundedBy {T : StdOp J} {C : ℝ} (hT : IsInnerBoundedBy T C) :
    T.IsBounded :=
  (isBoundedBy_of_isInnerBoundedBy hT).isBounded (abs_nonneg C)

end AmplifyOp

end

end GroupApproximation.Full.TWWSchafhauser
