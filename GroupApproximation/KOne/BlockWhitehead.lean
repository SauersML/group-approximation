import GroupApproximation.KOne.RankNElimination
import GroupApproximation.Meta.AxiomGuard

/-!
# Whitehead's identity in a two-index block of an arbitrary rank

`Leavitt/Whitehead.lean` proves `diag(a, a⁻¹) = w(a) · w(-1)` in rank two, in
the `!![ ; ]` notation, which does not survive a change of rank.  This file
proves the same identity in the block of two prescribed coordinates `l ≠ m` of
an arbitrary finite index type, and draws the consequence the unstable `K₁`
argument uses:

> `diagAt l ⁅u, v⁆ ∈ EL_ι(R)` for all units `u`, `v`, whenever `ι` has two
> distinct indices.

No hypothesis on `R` beyond `Ring R`: Whitehead's identity is unconditional,
and in particular nothing here needs the division property that
`RankNElimination` spends.

## The block calculus

`blockAt l m a b c d` is the matrix carrying `!![a, b; c, d]` in the
coordinates `l` and `m` and the identity elsewhere.  Two lemmas compute right
multiplication by an elementary matrix supported on those two coordinates, and
the six-factor Whitehead word is then five rewrites and some ring arithmetic.
-/

namespace GroupApproximation
namespace RankNElimination

open scoped commutatorElement

variable {R ι : Type*} [Ring R] [Fintype ι] [DecidableEq ι]

/-! ### A two-by-two block inside a matrix of arbitrary rank -/

/-- The matrix carrying `!![a, b; c, d]` in the coordinates `l` and `m`, and
the identity elsewhere. -/
def blockAt (l m : ι) (a b c d : R) : Matrix ι ι R :=
  Matrix.of fun x y ↦
    if x = l then (if y = l then a else if y = m then b else 0)
    else if x = m then (if y = l then c else if y = m then d else 0)
    else if x = y then 1 else 0

section Entries

variable (l m : ι) (a b c d : R)

omit [Fintype ι] in
theorem blockAt_apply (x y : ι) :
    blockAt l m a b c d x y =
      if x = l then (if y = l then a else if y = m then b else 0)
      else if x = m then (if y = l then c else if y = m then d else 0)
      else if x = y then 1 else 0 := rfl

omit [Fintype ι] in
theorem blockAt_ll : blockAt l m a b c d l l = a := by
  rw [blockAt_apply, if_pos rfl, if_pos rfl]

omit [Fintype ι] in
theorem blockAt_lm (hlm : l ≠ m) : blockAt l m a b c d l m = b := by
  rw [blockAt_apply, if_pos rfl, if_neg (Ne.symm hlm), if_pos rfl]

omit [Fintype ι] in
theorem blockAt_l_ne {y : ι} (hyl : y ≠ l) (hym : y ≠ m) :
    blockAt l m a b c d l y = 0 := by
  rw [blockAt_apply, if_pos rfl, if_neg hyl, if_neg hym]

omit [Fintype ι] in
theorem blockAt_ml (hlm : l ≠ m) : blockAt l m a b c d m l = c := by
  rw [blockAt_apply, if_neg (Ne.symm hlm), if_pos rfl, if_pos rfl]

omit [Fintype ι] in
theorem blockAt_mm (hlm : l ≠ m) : blockAt l m a b c d m m = d := by
  rw [blockAt_apply, if_neg (Ne.symm hlm), if_pos rfl, if_neg (Ne.symm hlm),
    if_pos rfl]

omit [Fintype ι] in
theorem blockAt_m_ne (hlm : l ≠ m) {y : ι} (hyl : y ≠ l) (hym : y ≠ m) :
    blockAt l m a b c d m y = 0 := by
  rw [blockAt_apply, if_neg (Ne.symm hlm), if_pos rfl, if_neg hyl, if_neg hym]

omit [Fintype ι] in
theorem blockAt_ne {x : ι} (hxl : x ≠ l) (hxm : x ≠ m) (y : ι) :
    blockAt l m a b c d x y = if x = y then 1 else 0 := by
  rw [blockAt_apply, if_neg hxl, if_neg hxm]

end Entries

omit [Fintype ι] in
theorem blockAt_one (l m : ι) (hlm : l ≠ m) :
    blockAt l m (1 : R) 0 0 1 = 1 := by
  ext x y
  by_cases hxl : x = l
  · rw [hxl]
    by_cases hyl : y = l
    · rw [hyl, blockAt_ll, Matrix.one_apply_eq]
    · rw [Matrix.one_apply_ne (fun h ↦ hyl h.symm)]
      by_cases hym : y = m
      · rw [hym, blockAt_lm _ _ _ _ _ _ hlm]
      · rw [blockAt_l_ne _ _ _ _ _ _ hyl hym]
  · by_cases hxm : x = m
    · rw [hxm]
      by_cases hyl : y = l
      · rw [hyl, blockAt_ml _ _ _ _ _ _ hlm,
          Matrix.one_apply_ne (Ne.symm hlm)]
      · by_cases hym : y = m
        · rw [hym, blockAt_mm _ _ _ _ _ _ hlm, Matrix.one_apply_eq]
        · rw [blockAt_m_ne _ _ _ _ _ _ hlm hyl hym,
            Matrix.one_apply_ne (fun h ↦ hym h.symm)]
    · rw [blockAt_ne _ _ _ _ _ _ hxl hxm, Matrix.one_apply]

omit [Fintype ι] in
theorem blockAt_diagonal (l m : ι) (hlm : l ≠ m) (a d : R) :
    blockAt l m a 0 0 d =
      Matrix.diagonal fun i ↦ if i = l then a else if i = m then d else 1 := by
  ext x y
  by_cases hxl : x = l
  · rw [hxl]
    by_cases hyl : y = l
    · rw [hyl, blockAt_ll, Matrix.diagonal_apply_eq, if_pos rfl]
    · rw [Matrix.diagonal_apply_ne _ (fun h ↦ hyl h.symm)]
      by_cases hym : y = m
      · rw [hym, blockAt_lm _ _ _ _ _ _ hlm]
      · rw [blockAt_l_ne _ _ _ _ _ _ hyl hym]
  · by_cases hxm : x = m
    · rw [hxm]
      by_cases hyl : y = l
      · rw [hyl, blockAt_ml _ _ _ _ _ _ hlm,
          Matrix.diagonal_apply_ne _ (Ne.symm hlm)]
      · by_cases hym : y = m
        · rw [hym, blockAt_mm _ _ _ _ _ _ hlm, Matrix.diagonal_apply_eq,
            if_neg (Ne.symm hlm), if_pos rfl]
        · rw [blockAt_m_ne _ _ _ _ _ _ hlm hyl hym,
            Matrix.diagonal_apply_ne _ (fun h ↦ hym h.symm)]
    · rw [blockAt_ne _ _ _ _ _ _ hxl hxm]
      by_cases hxy : x = y
      · have hyl : y ≠ l := fun h ↦ hxl (hxy.trans h)
        have hym : y ≠ m := fun h ↦ hxm (hxy.trans h)
        rw [if_pos hxy, hxy, Matrix.diagonal_apply_eq, if_neg hyl, if_neg hym]
      · rw [if_neg hxy, Matrix.diagonal_apply_ne _ hxy]

/-- Right multiplication by `x_{lm}(e)`: column `m` gains column `l` times
`e`. -/
theorem blockAt_mul_lm (l m : ι) (hlm : l ≠ m) (a b c d e : R) :
    blockAt l m a b c d * (elementaryUnit l m hlm e : Matrix ι ι R) =
      blockAt l m a (a * e + b) c (c * e + d) := by
  ext x y
  rw [mul_elementaryUnit_apply]
  by_cases hy : y = m
  · rw [hy, if_pos rfl]
    by_cases hxl : x = l
    · rw [hxl, blockAt_lm _ _ _ _ _ _ hlm, blockAt_ll,
        blockAt_lm _ _ _ _ _ _ hlm, add_comm]
    · by_cases hxm : x = m
      · rw [hxm, blockAt_mm _ _ _ _ _ _ hlm, blockAt_ml _ _ _ _ _ _ hlm,
          blockAt_mm _ _ _ _ _ _ hlm, add_comm]
      · rw [blockAt_ne _ _ _ _ _ _ hxl hxm, blockAt_ne _ _ _ _ _ _ hxl hxm,
          blockAt_ne _ _ _ _ _ _ hxl hxm, if_neg hxm, if_neg hxl, zero_mul,
          add_zero]
  · rw [if_neg hy]
    simp only [blockAt_apply, if_neg hy]

/-- Right multiplication by `x_{ml}(e)`: column `l` gains column `m` times
`e`. -/
theorem blockAt_mul_ml (l m : ι) (hlm : l ≠ m) (a b c d e : R) :
    blockAt l m a b c d * (elementaryUnit m l (Ne.symm hlm) e : Matrix ι ι R) =
      blockAt l m (b * e + a) b (d * e + c) d := by
  ext x y
  rw [mul_elementaryUnit_apply]
  by_cases hy : y = l
  · rw [hy, if_pos rfl]
    by_cases hxl : x = l
    · rw [hxl, blockAt_ll, blockAt_lm _ _ _ _ _ _ hlm, blockAt_ll, add_comm]
    · by_cases hxm : x = m
      · rw [hxm, blockAt_ml _ _ _ _ _ _ hlm, blockAt_mm _ _ _ _ _ _ hlm,
          blockAt_ml _ _ _ _ _ _ hlm, add_comm]
      · rw [blockAt_ne _ _ _ _ _ _ hxl hxm, blockAt_ne _ _ _ _ _ _ hxl hxm,
          blockAt_ne _ _ _ _ _ _ hxl hxm, if_neg hxl, if_neg hxm, zero_mul,
          add_zero]
  · rw [if_neg hy]
    simp only [blockAt_apply, if_neg hy]

/-! ### The Whitehead word -/

/-- The two-index diagonal unit carrying `u` at `l`, `v` at `m` and `1`
elsewhere. -/
def diagPairAt (l m : ι) (u v : Rˣ) : (Matrix ι ι R)ˣ where
  val := Matrix.diagonal fun i ↦
    if i = l then (u : R) else if i = m then (v : R) else 1
  inv := Matrix.diagonal fun i ↦
    if i = l then ((u⁻¹ : Rˣ) : R) else if i = m then ((v⁻¹ : Rˣ) : R) else 1
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal,
      show (1 : Matrix ι ι R) = Matrix.diagonal fun _ : ι ↦ (1 : R) from
        Matrix.diagonal_one.symm]
    refine congrArg Matrix.diagonal (funext fun i ↦ ?_)
    by_cases h : i = l
    · simp [h]
    · by_cases h2 : i = m
      · have hml : m ≠ l := fun hh ↦ h (h2.trans hh)
        simp [h2, hml]
      · simp [h, h2]
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal,
      show (1 : Matrix ι ι R) = Matrix.diagonal fun _ : ι ↦ (1 : R) from
        Matrix.diagonal_one.symm]
    refine congrArg Matrix.diagonal (funext fun i ↦ ?_)
    by_cases h : i = l
    · simp [h]
    · by_cases h2 : i = m
      · have hml : m ≠ l := fun hh ↦ h (h2.trans hh)
        simp [h2, hml]
      · simp [h, h2]

theorem diagPairAt_val (l m : ι) (u v : Rˣ) :
    ((diagPairAt l m u v : (Matrix ι ι R)ˣ) : Matrix ι ι R) =
      Matrix.diagonal fun i ↦
        if i = l then (u : R) else if i = m then (v : R) else 1 := rfl

theorem diagPairAt_mul (l m : ι) (u v u' v' : Rˣ) :
    (diagPairAt l m u v : (Matrix ι ι R)ˣ) * diagPairAt l m u' v' =
      diagPairAt l m (u * u') (v * v') := by
  apply Units.ext
  rw [Units.val_mul, diagPairAt_val, diagPairAt_val, diagPairAt_val,
    Matrix.diagonal_mul_diagonal]
  refine congrArg Matrix.diagonal (funext fun i ↦ ?_)
  by_cases h : i = l
  · simp [h]
  · by_cases h2 : i = m
    · have hml : m ≠ l := fun hh ↦ h (h2.trans hh)
      simp [h2, hml]
    · simp [h, h2]

theorem diagAt_eq_diagPairAt (l m : ι) (u : Rˣ) :
    (diagAt l u : (Matrix ι ι R)ˣ) = diagPairAt l m u 1 := by
  apply Units.ext
  rw [diagAt_val, diagPairAt_val]
  refine congrArg Matrix.diagonal (funext fun i ↦ ?_)
  by_cases h : i = l
  · simp [h]
  · by_cases h2 : i = m
    · have hml : m ≠ l := fun hh ↦ h (h2.trans hh)
      simp [h2, hml]
    · simp [h, h2]

omit [Fintype ι] in
theorem blockAt_congr (l m : ι) {a b c d a' b' c' d' : R} (ha : a = a')
    (hb : b = b') (hc : c = c') (hd : d = d') :
    blockAt l m a b c d = blockAt l m a' b' c' d' := by
  rw [ha, hb, hc, hd]

/-- **Whitehead's identity at two prescribed coordinates.**  The diagonal unit
`diag(x, x⁻¹)` in the coordinates `l` and `m` is a product of six elementary
matrices supported on those two coordinates. -/
theorem diagPairAt_self_inv_mem (l m : ι) (hlm : l ≠ m) (x : Rˣ) :
    (diagPairAt l m x x⁻¹ : (Matrix ι ι R)ˣ) ∈ elementaryGroup ι R := by
  have hxx : (x : R) * ((x⁻¹ : Rˣ) : R) = 1 := x.mul_inv
  have hxx' : ((x⁻¹ : Rˣ) : R) * (x : R) = 1 := x.inv_mul
  have p1 : ((elementaryUnit l m hlm (x : R) : (Matrix ι ι R)ˣ) :
      Matrix ι ι R) = blockAt l m (1 : R) (x : R) 0 1 := by
    have h := blockAt_mul_lm l m hlm (1 : R) 0 0 1 (x : R)
    rw [blockAt_one l m hlm, Matrix.one_mul] at h
    rw [h]
    exact blockAt_congr l m rfl (by noncomm_ring) rfl (by noncomm_ring)
  have p2 : ((elementaryUnit l m hlm (x : R) *
      elementaryUnit m l (Ne.symm hlm) (-((x⁻¹ : Rˣ) : R)) :
        (Matrix ι ι R)ˣ) : Matrix ι ι R) =
      blockAt l m 0 (x : R) (-((x⁻¹ : Rˣ) : R)) 1 := by
    rw [Units.val_mul, p1, blockAt_mul_ml l m hlm]
    exact blockAt_congr l m (by noncomm_ring [hxx]) rfl (by noncomm_ring) rfl
  have p3 : ((elementaryUnit l m hlm (x : R) *
      elementaryUnit m l (Ne.symm hlm) (-((x⁻¹ : Rˣ) : R)) *
      elementaryUnit l m hlm (x : R) : (Matrix ι ι R)ˣ) : Matrix ι ι R) =
      blockAt l m 0 (x : R) (-((x⁻¹ : Rˣ) : R)) 0 := by
    rw [Units.val_mul, p2, blockAt_mul_lm l m hlm]
    exact blockAt_congr l m rfl (by noncomm_ring) rfl
      (by noncomm_ring [hxx'])
  have p4 : ((elementaryUnit l m hlm (x : R) *
      elementaryUnit m l (Ne.symm hlm) (-((x⁻¹ : Rˣ) : R)) *
      elementaryUnit l m hlm (x : R) *
      elementaryUnit l m hlm (-1) : (Matrix ι ι R)ˣ) : Matrix ι ι R) =
      blockAt l m 0 (x : R) (-((x⁻¹ : Rˣ) : R)) ((x⁻¹ : Rˣ) : R) := by
    rw [Units.val_mul, p3, blockAt_mul_lm l m hlm]
    exact blockAt_congr l m rfl (by noncomm_ring) rfl (by noncomm_ring)
  have p5 : ((elementaryUnit l m hlm (x : R) *
      elementaryUnit m l (Ne.symm hlm) (-((x⁻¹ : Rˣ) : R)) *
      elementaryUnit l m hlm (x : R) *
      elementaryUnit l m hlm (-1) *
      elementaryUnit m l (Ne.symm hlm) 1 : (Matrix ι ι R)ˣ) : Matrix ι ι R) =
      blockAt l m (x : R) (x : R) 0 ((x⁻¹ : Rˣ) : R) := by
    rw [Units.val_mul, p4, blockAt_mul_ml l m hlm]
    exact blockAt_congr l m (by noncomm_ring) rfl (by noncomm_ring) rfl
  have p6 : ((elementaryUnit l m hlm (x : R) *
      elementaryUnit m l (Ne.symm hlm) (-((x⁻¹ : Rˣ) : R)) *
      elementaryUnit l m hlm (x : R) *
      elementaryUnit l m hlm (-1) *
      elementaryUnit m l (Ne.symm hlm) 1 *
      elementaryUnit l m hlm (-1) : (Matrix ι ι R)ˣ) : Matrix ι ι R) =
      blockAt l m (x : R) 0 0 ((x⁻¹ : Rˣ) : R) := by
    rw [Units.val_mul, p5, blockAt_mul_lm l m hlm]
    exact blockAt_congr l m rfl (by noncomm_ring) rfl (by noncomm_ring)
  have hPeq : (diagPairAt l m x x⁻¹ : (Matrix ι ι R)ˣ) =
      elementaryUnit l m hlm (x : R) *
        elementaryUnit m l (Ne.symm hlm) (-((x⁻¹ : Rˣ) : R)) *
        elementaryUnit l m hlm (x : R) *
        elementaryUnit l m hlm (-1) *
        elementaryUnit m l (Ne.symm hlm) 1 *
        elementaryUnit l m hlm (-1) := by
    apply Units.ext
    rw [p6, blockAt_diagonal l m hlm, diagPairAt_val]
  rw [hPeq]
  exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem
    (elementaryUnit_mem _ _ _ _) (elementaryUnit_mem _ _ _ _))
    (elementaryUnit_mem _ _ _ _)) (elementaryUnit_mem _ _ _ _))
    (elementaryUnit_mem _ _ _ _)) (elementaryUnit_mem _ _ _ _)

/-! ### The commutator consequence -/

/-- `u ↦ diagAt l u` as a homomorphism. -/
def diagAtHom (l : ι) : Rˣ →* (Matrix ι ι R)ˣ where
  toFun u := diagAt l u
  map_one' := by
    apply Units.ext
    simp only [diagAt_val, Units.val_one]
    rw [← Matrix.diagonal_one]
    exact congrArg Matrix.diagonal (funext fun _ ↦ by simp)
  map_mul' u v := by
    apply Units.ext
    rw [Units.val_mul, diagAt_val, diagAt_val, diagAt_val,
      Matrix.diagonal_mul_diagonal]
    refine congrArg Matrix.diagonal (funext fun i ↦ ?_)
    by_cases h : i = l <;> simp [h]

theorem diagAtHom_apply (l : ι) (u : Rˣ) :
    diagAtHom l u = (diagAt l u : (Matrix ι ι R)ˣ) := rfl

/-- **The commutator of two units lands in the elementary group after the
diagonal embedding.**  This is Whitehead's lemma in the form the unstable `K₁`
argument uses, and it holds over every ring. -/
theorem diagAt_commutatorElement_mem (l m : ι) (hlm : l ≠ m) (u v : Rˣ) :
    (diagAt l ⁅u, v⁆ : (Matrix ι ι R)ˣ) ∈ elementaryGroup ι R := by
  have hsplit : (diagAt l ⁅u, v⁆ : (Matrix ι ι R)ˣ) =
      diagPairAt l m (u * v) (u * v)⁻¹ *
        diagPairAt l m u⁻¹ (u⁻¹)⁻¹ * diagPairAt l m v⁻¹ (v⁻¹)⁻¹ := by
    have hone : (u * v)⁻¹ * (u⁻¹)⁻¹ * (v⁻¹)⁻¹ = (1 : Rˣ) := by group
    rw [diagPairAt_mul, diagPairAt_mul, hone, diagAt_eq_diagPairAt l m,
      commutatorElement_def]
  rw [hsplit]
  exact mul_mem (mul_mem (diagPairAt_self_inv_mem l m hlm _)
    (diagPairAt_self_inv_mem l m hlm _)) (diagPairAt_self_inv_mem l m hlm _)

/-- **The diagonal embedding carries the whole commutator subgroup of `Rˣ` into
`EL_ι(R)`.**  Whitehead's identity applied to the generators of `commutator Rˣ`,
so this needs no hypothesis on `R` at all: not nontriviality, not a division
property, not the elimination of `RankNElimination`.

This is the form `AGPStepOne` consumes: `v ∈ commutator Rˣ` is exactly what
`κ v = 1` supplies there, and the conclusion is `diag(v, 1, …, 1) ∈ EL_ι(R)`
with no K-theory colimit in between.  `UnstableKOneAbelian.commutator_le_elementaryGroup`
reaches the same conclusion but carries `Nontrivial R` and single-sandwich
division, which this does not need.

## Its neighbours in this namespace

`KOne/DiagonalCommutatorElementary.lean` declares into the same namespace and
holds two lemmas about the same embedding.  They are not interchangeable with
this one and only one of them is superseded:

* `diagAt_mem_commutator_of_mem` --- `v ∈ commutator Rˣ → diagAt l v ∈
  commutator (Matrix ι ι R)ˣ`, hypothesis-free.  **Not** superseded: its
  conclusion lands in the commutator subgroup of `GL_ι(R)`, which is a
  different and sometimes more useful place than `EL_ι(R)`, and nothing here
  provides it.
* `diagAt_mem_elementaryGroup_of_mem_commutator` --- same conclusion as this
  lemma but with `Nontrivial R` and `HasSingleSandwichDivision R`, because it
  factors through `commutator_le_elementaryGroup`.  Prefer this one whenever
  the ring has no division property to hand; the two agree whenever both
  apply. -/
theorem diagAt_commutator_mem (l m : ι) (hlm : l ≠ m) {v : Rˣ}
    (hv : v ∈ commutator Rˣ) :
    (diagAt l v : (Matrix ι ι R)ˣ) ∈ elementaryGroup ι R := by
  have hle : commutator Rˣ ≤ (elementaryGroup ι R).comap (diagAtHom l) := by
    rw [commutator_def, Subgroup.commutator_le]
    intro u _ w _
    show (diagAtHom l) ⁅u, w⁆ ∈ elementaryGroup ι R
    rw [diagAtHom_apply]
    exact diagAt_commutatorElement_mem l m hlm u w
  exact hle hv

end RankNElimination
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.RankNElimination.diagPairAt_self_inv_mem
#audit_axioms GroupApproximation.RankNElimination.diagAt_commutator_mem
