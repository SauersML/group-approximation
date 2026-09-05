import GroupApproximation.Analysis.FiniteCStarMurrayVonNeumann
import GroupApproximation.Analysis.LIXProjectiveSpaceModel

/-!
# Complex vector bundles in the projection model, I: the objects

Throughout the STW Problem LIX programme a *complex vector bundle* over a
compact Hausdorff space `X` **is** a continuous projection-valued matrix
function on `X`, an *isomorphism of bundles* **is** a continuous Murray-von
Neumann equivalence of such projections, and there is no bundle library and no
Serre-Swan theorem anywhere.  This file fixes the object.

## The index type is arbitrary, not `Fin K`

The bundles the campaign actually manipulates are indexed by
`EIdx i = Fin 2 ⊕ HIdx i` (`Analysis/LIXBlockProjections.lean`), and the
constructions below take block sums repeatedly.  Indexing by `Fin K` would force
a `Fin (K + K')`-versus-`Fin K ⊕ Fin K'` cast at every block sum; indexing by an
arbitrary `ι : Type` with `[Fintype ι]` makes the block sum *definitionally*
`Matrix.fromBlocks` over `ι ⊕ κ`, with no arithmetic at all.  `Fin`-indexed
statements are recovered by instantiating `ι := Fin K`; the one place where a
genuine `Fin (d+1)` is needed is the comparison with
`Analysis/LIXProjectiveSpaceModel.lean`'s `CP d`, and that comparison is a
single lemma in `BundleSpace.lean`.

## Two spellings of the same object

`Matrix ι ι C(X, ℂ)` (the spelling of `KTheory/MatrixProjection.lean` and of
`Analysis/LIXBlockProjections.lean`) and `Bundle X ι` are interchanged by
`Bundle.ofMatrixSection` / `Bundle.toMatrixSection`, which are mutually inverse
and match `STW59.matEval` on the nose.  This is the bridge
`AlgTop/BundleCalculusModelBridge.lean` supplies for `C(X, CStarMatrix ι ι ℂ)`,
in the norm-free form the topology lanes need: **no norm on `Matrix` is used
anywhere in this lane**, because there is no norm instance on `Matrix` at the
Mathlib pin.

## Manuscript status

Machinery for Lemma 2 (`notes/LIX_FULL_PROGRAM_2026-09-05.md` §1.3); certifies
no manuscript step on its own.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass

open scoped Matrix
open GroupApproximation.STW59

/-! ### One positivity input

The only fact about `ℂ` that the algebra below needs is that `Aᴴ A = 0` forces
`A = 0`.  Mathlib's `Matrix.conjTranspose_mul_self_eq_zero` proves it, but only
for a `StarOrderedRing`, which for `ℂ` means dragging in `ComplexOrder` and its
instance ladder.  The entrywise proof is four lines and keeps this lane
order-free. -/

theorem eq_zero_of_conjTranspose_mul_self {ι κ : Type} [Fintype ι] [Fintype κ]
    {w : Matrix κ ι ℂ} (h : wᴴ * w = 0) : w = 0 := by
  ext k i
  have hdiag : (∑ l, ‖w l i‖ ^ 2 : ℝ) = 0 := by
    have h1 : (wᴴ * w) i i = ((∑ l, ‖w l i‖ ^ 2 : ℝ) : ℂ) := by
      rw [Matrix.mul_apply, Complex.ofReal_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Matrix.conjTranspose_apply]
      exact star_mul_self_eq_normSq (w l i)
    have h2 : ((∑ l, ‖w l i‖ ^ 2 : ℝ) : ℂ) = ((0 : ℝ) : ℂ) := by
      rw [← h1, h, Matrix.zero_apply, Complex.ofReal_zero]
    exact_mod_cast h2
  have hzero : ‖w k i‖ ^ 2 = 0 := by
    have hnn : ∀ l ∈ (Finset.univ : Finset κ), (0 : ℝ) ≤ ‖w l i‖ ^ 2 := fun l _ => by positivity
    exact (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hdiag k (Finset.mem_univ k)
  have : ‖w k i‖ = 0 := by nlinarith [norm_nonneg (w k i)]
  simpa using this

/-- **A complex vector bundle over `X`**, in the projection model: a continuous
family of orthogonal projections in `Matrix ι ι ℂ`.  The fibre over `x` is the
range of `p x`, and the rank is the trace, which is a natural number
(`STW59.exists_natCast_trace`) and locally constant (`BundleLocal.lean`). -/
structure Bundle (X : Type) [TopologicalSpace X] (ι : Type) [Fintype ι] where
  /-- The projection at a point of the base.  Use the `FunLike` coercion. -/
  toFun : X → Matrix ι ι ℂ
  continuous_toFun : Continuous toFun
  isStarProjection_toFun : ∀ x, IsStarProjection (toFun x)

namespace Bundle

section Basic

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι]

instance instFunLike : FunLike (Bundle X ι) X (Matrix ι ι ℂ) where
  coe p := p.toFun
  coe_injective p q h := by
    cases p
    cases q
    congr

@[simp]
theorem toFun_eq_coe (p : Bundle X ι) : p.toFun = ⇑p := rfl

@[simp]
theorem coe_mk (f : X → Matrix ι ι ℂ) (hc : Continuous f)
    (hp : ∀ x, IsStarProjection (f x)) : ⇑(Bundle.mk f hc hp) = f := rfl

@[ext]
theorem ext {p q : Bundle X ι} (h : ∀ x, p x = q x) : p = q := DFunLike.ext _ _ h

protected theorem continuous (p : Bundle X ι) : Continuous (p : X → Matrix ι ι ℂ) :=
  p.continuous_toFun

protected theorem isStarProjection (p : Bundle X ι) (x : X) : IsStarProjection (p x) :=
  p.isStarProjection_toFun x

theorem mul_self (p : Bundle X ι) (x : X) : p x * p x = p x :=
  (p.isStarProjection x).isIdempotentElem.eq

theorem conjTranspose_eq (p : Bundle X ι) (x : X) : (p x)ᴴ = p x :=
  conjTranspose_eq_of_isStarProjection (p.isStarProjection x)

/-- A vector obtained by applying the projection is fixed by it: the fibre is
the fixed-point set.  Membership in a fibre is always written `p x *ᵥ v = v`
below, because that form is what the continuity arguments consume. -/
theorem mulVec_mulVec_self (p : Bundle X ι) (x : X) (v : ι → ℂ) :
    p x *ᵥ (p x *ᵥ v) = p x *ᵥ v := by
  rw [Matrix.mulVec_mulVec, p.mul_self]

end Basic

/-! ### The rank -/

section Rank

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι]

/-- The rank of a bundle at a point: the trace of the projection, which is a
natural number by `STW59.exists_natCast_trace` (proved there without the
spectral theorem). -/
noncomputable def rank (p : Bundle X ι) (x : X) : ℕ :=
  (exists_natCast_trace (p.isStarProjection x)).choose

theorem trace_eq_rank (p : Bundle X ι) (x : X) : (p x).trace = (p.rank x : ℂ) :=
  (exists_natCast_trace (p.isStarProjection x)).choose_spec

theorem rank_eq_of_trace_eq {p : Bundle X ι} {q : Bundle X ι} {x y : X}
    (h : (p x).trace = (q y).trace) : p.rank x = q.rank y := by
  have h' : ((p.rank x : ℕ) : ℂ) = ((q.rank y : ℕ) : ℂ) := by
    rw [← trace_eq_rank, ← trace_eq_rank]
    exact h
  exact_mod_cast h'

theorem continuous_trace (p : Bundle X ι) : Continuous fun x => (p x).trace :=
  p.continuous.matrix_trace

end Rank

/-! ### The elementary constructions -/

section Constructions

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
variable {ι κ : Type} [Fintype ι] [Fintype κ]

/-- The trivial bundle of rank `#ι`. -/
def triv (X : Type) [TopologicalSpace X] (ι : Type) [Fintype ι] [DecidableEq ι] :
    Bundle X ι where
  toFun _ := 1
  continuous_toFun := continuous_const
  isStarProjection_toFun _ := IsStarProjection.one _

@[simp]
theorem triv_apply [DecidableEq ι] (x : X) : triv X ι x = 1 := rfl

/-- **Pullback along a continuous map of bases**, `f^* p = p ∘ f`. -/
def comap (f : C(Y, X)) (p : Bundle X ι) : Bundle Y ι where
  toFun y := p (f y)
  continuous_toFun := p.continuous.comp f.continuous
  isStarProjection_toFun y := p.isStarProjection (f y)

@[simp]
theorem comap_apply (f : C(Y, X)) (p : Bundle X ι) (y : Y) : comap f p y = p (f y) := rfl

theorem comap_id (p : Bundle X ι) : comap (ContinuousMap.id X) p = p := rfl

theorem comap_comp {Z : Type} [TopologicalSpace Z] (g : C(Z, Y)) (f : C(Y, X))
    (p : Bundle X ι) : comap g (comap f p) = comap (f.comp g) p := rfl

/-- **Block sum of bundles**, the Whitney sum in the projection model. -/
def blockSum (p : Bundle X ι) (q : Bundle X κ) : Bundle X (ι ⊕ κ) where
  toFun x := Matrix.fromBlocks (p x) 0 0 (q x)
  continuous_toFun := by
    refine continuous_matrix fun i j => ?_
    cases i with
    | inl i =>
        cases j with
        | inl j => exact p.continuous.matrix_elem i j
        | inr j => exact continuous_const
    | inr i =>
        cases j with
        | inl j => exact continuous_const
        | inr j => exact q.continuous.matrix_elem i j
  isStarProjection_toFun x := by
    rw [isStarProjection_matrix_iff]
    constructor
    · simp only [Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero, p.conjTranspose_eq,
        q.conjTranspose_eq]
    · rw [Matrix.fromBlocks_multiply]
      simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, p.mul_self, q.mul_self]

@[simp]
theorem blockSum_apply (p : Bundle X ι) (q : Bundle X κ) (x : X) :
    blockSum p q x = Matrix.fromBlocks (p x) 0 0 (q x) := rfl

/-- The trace of a block matrix splits.  Mathlib has no `fromBlocks` lemma for
the trace, and `Analysis/LIXBlockProjections.lean`'s copy is in a module this
lane does not import. -/
theorem trace_fromBlocks {A : Matrix ι ι ℂ} {B : Matrix ι κ ℂ} {C : Matrix κ ι ℂ}
    {D : Matrix κ κ ℂ} : (Matrix.fromBlocks A B C D).trace = A.trace + D.trace := by
  simp [Matrix.trace, Matrix.diag, Fintype.sum_sum_type]

theorem trace_blockSum (p : Bundle X ι) (q : Bundle X κ) (x : X) :
    (blockSum p q x).trace = (p x).trace + (q x).trace := trace_fromBlocks

/-- Adding a trivial line to a bundle: the ambient bundle of the projective
completion `P(p ⊕ 1)`. -/
def plusOne (p : Bundle X ι) : Bundle X (ι ⊕ Unit) := blockSum p (triv X Unit)

@[simp]
theorem plusOne_apply (p : Bundle X ι) (x : X) :
    p.plusOne x = Matrix.fromBlocks (p x) 0 0 1 := rfl

end Constructions

/-! ### The bridge with `Matrix ι ι C(X, ℂ)`

`Analysis/LIXBlockProjections.lean` and `KTheory/MatrixProjection.lean` present a
bundle as a projection in `Matrix ι ι C(X, ℂ)`.  The two presentations are the
same data; `STW59.matEval` is the comparison map, and the two directions below
are mutually inverse. -/

section MatrixSection

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι]

/-- A bundle read as a matrix of continuous scalar functions. -/
def toMatrixSection (p : Bundle X ι) : Matrix ι ι C(X, ℂ) :=
  Matrix.of fun i j => ⟨fun x => p x i j, p.continuous.matrix_elem i j⟩

@[simp]
theorem toMatrixSection_apply (p : Bundle X ι) (i j : ι) (x : X) :
    p.toMatrixSection i j x = p x i j := rfl

@[simp]
theorem matEval_toMatrixSection (p : Bundle X ι) (x : X) :
    matEval x p.toMatrixSection = p x := rfl

theorem isStarProjection_toMatrixSection (p : Bundle X ι) :
    IsStarProjection p.toMatrixSection := by
  refine isStarProjection_of_forall_matEval fun x => ?_
  rw [matEval_toMatrixSection]
  exact p.isStarProjection x

/-- A projection in `Matrix ι ι C(X, ℂ)` read as a bundle. -/
noncomputable def ofMatrixSection (P : Matrix ι ι C(X, ℂ)) (hP : IsStarProjection P) :
    Bundle X ι where
  toFun x := matEval x P
  continuous_toFun := continuous_matrix fun i j => map_continuous (P i j)
  isStarProjection_toFun x := isStarProjection_matEval hP x

@[simp]
theorem ofMatrixSection_apply (P : Matrix ι ι C(X, ℂ)) (hP : IsStarProjection P) (x : X) :
    ofMatrixSection P hP x = matEval x P := rfl

theorem ofMatrixSection_toMatrixSection (p : Bundle X ι) :
    ofMatrixSection p.toMatrixSection p.isStarProjection_toMatrixSection = p := rfl

theorem toMatrixSection_ofMatrixSection (P : Matrix ι ι C(X, ℂ))
    (hP : IsStarProjection P) : (ofMatrixSection P hP).toMatrixSection = P :=
  matrix_ext_of_matEval fun _ => rfl

end MatrixSection

end Bundle

/-! ### Isomorphism of bundles

An isomorphism is a continuous family of partial isometries: exactly a
Murray-von Neumann equivalence in `Matrix ι ι C(X, ℂ)`, written pointwise, and
allowed to be *rectangular* so that bundles of different ambient sizes can be
compared (`L ⊆ X × ℂ^K` isomorphic to `L' ⊆ X × ℂ^{K'}` is the hypothesis of the
classifying-map statement in `BundleInvariance.lean`). -/

/-- **Isomorphism of bundles**: a continuous family `v x : Matrix κ ι ℂ` with
`(v x)ᴴ (v x) = p x` and `(v x) (v x)ᴴ = q x`.  For `κ = ι` this is exactly
`GroupApproximation.MurrayVonNeumannEquiv` in `Matrix ι ι C(X, ℂ)`
(`BundleIso.murrayVonNeumannEquiv` and `BundleIso.ofMurrayVonNeumannEquiv`). -/
structure BundleIso {X : Type} [TopologicalSpace X] {ι κ : Type} [Fintype ι] [Fintype κ]
    (p : Bundle X ι) (q : Bundle X κ) where
  /-- The implementing family of partial isometries. -/
  hom : X → Matrix κ ι ℂ
  continuous_hom : Continuous hom
  conjTranspose_mul : ∀ x, (hom x)ᴴ * hom x = p x
  mul_conjTranspose : ∀ x, hom x * (hom x)ᴴ = q x

namespace BundleIso

section

variable {X : Type} [TopologicalSpace X] {ι κ : Type} [Fintype ι] [Fintype κ]
variable {p : Bundle X ι} {q : Bundle X κ}

/-- Every bundle is isomorphic to itself, implemented by the projection. -/
def refl (p : Bundle X ι) : BundleIso p p where
  hom := fun x => p x
  continuous_hom := p.continuous
  conjTranspose_mul x := by rw [p.conjTranspose_eq x]; exact p.mul_self x
  mul_conjTranspose x := by rw [p.conjTranspose_eq x]; exact p.mul_self x

/-- Adjointing the implementer reverses an isomorphism. -/
def symm (e : BundleIso p q) : BundleIso q p where
  hom := fun x => (e.hom x)ᴴ
  continuous_hom := e.continuous_hom.matrix_conjTranspose
  conjTranspose_mul x := by
    rw [Matrix.conjTranspose_conjTranspose]
    exact e.mul_conjTranspose x
  mul_conjTranspose x := by
    rw [Matrix.conjTranspose_conjTranspose]
    exact e.conjTranspose_mul x

/-- Composing implementers composes isomorphisms. -/
def trans {ρ : Type} [Fintype ρ] {r : Bundle X ρ} (e : BundleIso p q) (f : BundleIso q r) :
    BundleIso p r where
  hom := fun x => f.hom x * e.hom x
  continuous_hom := f.continuous_hom.matrix_mul e.continuous_hom
  conjTranspose_mul x := by
    rw [Matrix.conjTranspose_mul]
    calc (e.hom x)ᴴ * (f.hom x)ᴴ * (f.hom x * e.hom x)
        = (e.hom x)ᴴ * ((f.hom x)ᴴ * f.hom x) * e.hom x := by
          simp only [Matrix.mul_assoc]
      _ = (e.hom x)ᴴ * (e.hom x * (e.hom x)ᴴ) * e.hom x := by
          rw [f.conjTranspose_mul, e.mul_conjTranspose]
      _ = ((e.hom x)ᴴ * e.hom x) * ((e.hom x)ᴴ * e.hom x) := by
          simp only [Matrix.mul_assoc]
      _ = p x * p x := by rw [e.conjTranspose_mul]
      _ = p x := p.mul_self x
  mul_conjTranspose x := by
    rw [Matrix.conjTranspose_mul]
    calc f.hom x * e.hom x * ((e.hom x)ᴴ * (f.hom x)ᴴ)
        = f.hom x * (e.hom x * (e.hom x)ᴴ) * (f.hom x)ᴴ := by simp only [Matrix.mul_assoc]
      _ = f.hom x * ((f.hom x)ᴴ * f.hom x) * (f.hom x)ᴴ := by
          rw [e.mul_conjTranspose, f.conjTranspose_mul]
      _ = (f.hom x * (f.hom x)ᴴ) * (f.hom x * (f.hom x)ᴴ) := by simp only [Matrix.mul_assoc]
      _ = r x * r x := by rw [f.mul_conjTranspose]
      _ = r x := r.mul_self x

/-- The implementer absorbs the source projection on the right.  This is the
`v v* v = v` identity, and the only place the positivity of `ℂ` enters the
algebra of isomorphisms. -/
theorem hom_mul_right (e : BundleIso p q) (x : X) : e.hom x * p x = e.hom x := by
  have hstep : (e.hom x)ᴴ * (e.hom x * p x - e.hom x) = 0 := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, e.conjTranspose_mul, p.mul_self, sub_self]
  have hkey : (e.hom x * p x - e.hom x)ᴴ * (e.hom x * p x - e.hom x) = 0 := by
    have hct : (e.hom x * p x - e.hom x)ᴴ = p x * (e.hom x)ᴴ - (e.hom x)ᴴ := by
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, p.conjTranspose_eq]
    rw [hct, Matrix.sub_mul, Matrix.mul_assoc, hstep, Matrix.mul_zero, sub_self]
  exact sub_eq_zero.mp (eq_zero_of_conjTranspose_mul_self hkey)

/-- The implementer absorbs the target projection on the left.  Same argument
mirrored; it is not obtained from `hom_mul_right` by `symm`, because
`(BundleIso.symm e).hom` does not reduce syntactically to `(e.hom ·)ᴴ` in a
`rw` chain. -/
theorem hom_mul_left (e : BundleIso p q) (x : X) : q x * e.hom x = e.hom x := by
  have hstep : (q x * e.hom x - e.hom x) * (e.hom x)ᴴ = 0 := by
    rw [Matrix.sub_mul, Matrix.mul_assoc, e.mul_conjTranspose, q.mul_self, sub_self]
  have hkey : ((q x * e.hom x - e.hom x)ᴴ)ᴴ * (q x * e.hom x - e.hom x)ᴴ = 0 := by
    rw [Matrix.conjTranspose_conjTranspose]
    have hct : (q x * e.hom x - e.hom x)ᴴ = (e.hom x)ᴴ * q x - (e.hom x)ᴴ := by
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, q.conjTranspose_eq]
    rw [hct, Matrix.mul_sub, ← Matrix.mul_assoc, hstep, Matrix.zero_mul, sub_self]
  have hz := congrArg Matrix.conjTranspose (eq_zero_of_conjTranspose_mul_self hkey)
  rw [Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_zero] at hz
  exact sub_eq_zero.mp hz

/-- **A bundle isomorphism is a Murray-von Neumann equivalence** in the repo's
sense, in `Matrix ι ι C(X, ℂ)`, when the two ambient sizes agree. -/
theorem murrayVonNeumannEquiv {q' : Bundle X ι} (e : BundleIso p q') :
    MurrayVonNeumannEquiv p.toMatrixSection q'.toMatrixSection := by
  refine ⟨Matrix.of fun i j => ⟨fun x => e.hom x i j, e.continuous_hom.matrix_elem i j⟩, ?_, ?_⟩
  · refine matrix_ext_of_matEval fun x => ?_
    rw [Matrix.star_eq_conjTranspose, matEval_mul, matEval_conjTranspose,
      Bundle.matEval_toMatrixSection]
    exact e.conjTranspose_mul x
  · refine matrix_ext_of_matEval fun x => ?_
    rw [Matrix.star_eq_conjTranspose, matEval_mul, matEval_conjTranspose,
      Bundle.matEval_toMatrixSection]
    exact e.mul_conjTranspose x

/-- The converse: a Murray-von Neumann equivalence of the two matrices of
functions is a bundle isomorphism.  Continuity of the implementer is automatic,
because its entries are continuous functions by construction. -/
noncomputable def ofMurrayVonNeumannEquiv {q' : Bundle X ι}
    (h : MurrayVonNeumannEquiv p.toMatrixSection q'.toMatrixSection) : BundleIso p q' where
  hom := fun x => matEval x h.choose
  continuous_hom := continuous_matrix fun i j => map_continuous (h.choose i j)
  conjTranspose_mul x := by
    have hx := h.choose_spec.1
    have := congrArg (matEval x) hx
    rwa [Matrix.star_eq_conjTranspose, matEval_mul, matEval_conjTranspose,
      Bundle.matEval_toMatrixSection] at this
  mul_conjTranspose x := by
    have hx := h.choose_spec.2
    have := congrArg (matEval x) hx
    rwa [Matrix.star_eq_conjTranspose, matEval_mul, matEval_conjTranspose,
      Bundle.matEval_toMatrixSection] at this

end

end BundleIso

end CharClass
end GroupApproximation
