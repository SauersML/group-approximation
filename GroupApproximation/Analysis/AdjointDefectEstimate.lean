import GroupApproximation.Sofic.PrintedReverseTransportRoute

/-!
# The adjoint defect estimate, read on the matrix algebra itself

Section 3 of `non_mf_groups_exist.tex` opens the proof of
`\begin{theorem}[one-sided Kazhdan transport]\label{thm:transport}` with two
sub-steps.  First a displayed estimate: for unitaries `A, B`,
\[
  \|\operatorname{Ad}(A)-\operatorname{Ad}(B)\| \le 2\|A-B\| ,
\]
and then its consequence, *"so the operator-norm multiplicative defects of
`(V_n)` also make the conjugation actions multiplicative modulo `c_0`"*.  The
paragraph closes with the remark that, after choosing matrix units, the
coordinate operators `Ad(V_n(g))` live in a norm matrix corona with coordinate
sizes `d_n^2`.

## What the corpus already had, and in which picture

The printed proof regards each `M_{d_n}(ℂ)` as a **Hilbert space** for the
normalized Hilbert--Schmidt inner product, so the displayed `‖·‖` there is the
operator norm of a superoperator acting on that Hilbert space.  In that picture
all three sub-steps are already proved, in `Sofic/AdjointMatrix.lean`:

* `l2_opNorm_conjDouble_sub_le_two` is the displayed estimate.  `conjDouble U`
  is the matrix of `X ↦ U X U⋆` in row-major pair coordinates, so its `L²`
  operator norm on `Matrix (Y × Y) (Y × Y) ℂ` *is* `‖Ad(U)‖` on the
  Hilbert--Schmidt space (normalizing the inner product rescales it by a
  constant and so leaves the operator norm unchanged).
* `l2_opNorm_conjDouble_defect_le` and
  `OpAlmostRepresentation.adjoint.asymptoticallyMultiplicative` are the
  consequence, and `OpAlmostRepresentation.adjoint` is the packaging.
* `UltraproductModelConstruction.piHom` even carries the packaging the rest of
  the way, into the unitary group of the corona.

**Nothing below reproves any of that.**  This file supplies the two things the
corpus did not have.

## What is new here

*The other picture.*  `Ad(U)` also acts on `M_d(ℂ)` carrying its **own**
operator norm --- the C⋆-norm, not the Hilbert--Schmidt one.  `adConj` is that
action, `opNorm_adConj_sub_le_two_mul` is the displayed estimate for it, and
`OpAlmostRepresentation.adConj_asymptoticallyMultiplicative` is the consequence,
stated in the same shape as `OpAlmostRepresentation.asymptoticallyMultiplicative`.
The estimate is not reproved either: it is
`KazhdanAsymptoticCommutant.opNorm_conj_sub_conj_le` at the sharp bound
`M = ‖X‖`, which is where the printed identity
`A X A⋆ - B X B⋆ = (A-B) X A⋆ + B X (A⋆-B⋆)` is actually discharged.

This picture is **not** the corona picture, and nothing here claims it is: the
manuscript's `B(M_{d_n}(ℂ))` is the bounded operators on `M_{d_n}(ℂ)` *as a
Hilbert space*, which is the `conjDouble` picture and is what makes the corona a
C⋆-algebra.  Bounded maps of `M_d(ℂ)` to itself in the C⋆-norm form a Banach
algebra, not a C⋆-algebra, and no corona is built from them below.  What the
operator-norm reading is good for is the shape in which the estimate is
consumed downstream, against a *uniformly bounded* sequence `(x_n)` --- the
hypothesis `thm:transport` actually carries --- where the Hilbert--Schmidt
operator norm of `Ad(U) - Ad(V)` is not the quantity being controlled.

*The coordinate sizes.*  `OpAlmostRepresentation.naturalizeCoordinates` is the
choice of matrix units: it replaces every finite model by the literal natural
basis `Fin (card)` of the same cardinality, isometrically, by the reindexing of
`Analysis/NaturalMatrixCoordinateEquiv` and `Analysis/MatrixReindexHilbertSchmidt`.
`card_adjoint_naturalizeCoordinates_model` is then the manuscript's remark in
the only form it has content in: the adjoint model, read on matrix units, has
coordinate sizes exactly `d_n^2`.

## What is *not* claimed

`naturalizeCoordinates` does not build the corona, and no declaration here says
that `g ↦ [Ad(V_n(g))]` is an exact homomorphism into its unitary group; that
is `UltraproductModelConstruction.piHom`, over the doubled index, and the
present file only records that the doubled index is `d_n^2` points once matrix
units are chosen.
-/

namespace GroupApproximation

open Matrix GeneralModelTransport
open scoped Matrix.Norms.L2Operator

universe u

noncomputable section

/-! ## `Ad` as a map of the matrix algebra -/

/-- `Ad U` on matrix coordinates: `X ↦ U X U⋆`.  Unlike `conjDouble`, which is
the same map written as a matrix on the doubled index and therefore measured in
the Hilbert--Schmidt norm, this is the map of the C⋆-algebra `M_d(ℂ)` to
itself. -/
def adConj {Y : FiniteModel} (U X : Matrix Y Y ℂ) : Matrix Y Y ℂ := U * X * Uᴴ

@[simp] theorem adConj_apply {Y : FiniteModel} (U X : Matrix Y Y ℂ) :
    adConj U X = U * X * Uᴴ := rfl

/-- `Ad` of the identity is the identity. -/
theorem adConj_one {Y : FiniteModel} (X : Matrix Y Y ℂ) :
    adConj (1 : Matrix Y Y ℂ) X = X := by
  rw [adConj_apply, Matrix.conjTranspose_one, mul_one, one_mul]

/-- **`Ad` is exactly multiplicative**, with no hypothesis on `U` or `V` at
all: `Ad(UV) = Ad(U) ∘ Ad(V)`.  This is what turns the operator-norm defect of
`(V_n)` into the defect of the conjugation actions, with the estimate below
supplying the constant. -/
theorem adConj_mul {Y : FiniteModel} (U V X : Matrix Y Y ℂ) :
    adConj (U * V) X = adConj U (adConj V X) := by
  rw [adConj_apply, adConj_apply, adConj_apply, Matrix.conjTranspose_mul]
  noncomm_ring

/-! ## The displayed estimate -/

/-- **The manuscript's displayed adjoint estimate, on the matrix algebra with
its own operator norm.**  For unitary `U, V` and every `X`,

`‖U X U⋆ - V X V⋆‖ ≤ 2 ‖U - V‖ ‖X‖`,

which is the bound `‖Ad(U) - Ad(V)‖ ≤ 2‖U - V‖` on the superoperator.

The printed proof --- `U X U⋆ - V X V⋆ = (U-V) X U⋆ + V X (U⋆-V⋆)`,
submultiplicativity, and `‖U⋆‖ = ‖U‖ = 1` --- is
`KazhdanAsymptoticCommutant.opNorm_conj_sub_conj_le`, which is stated against an
arbitrary uniform bound `M ≥ ‖X‖`; this is that bound at `M = ‖X‖`, where it
becomes the estimate on the superoperator rather than on one uniformly bounded
sequence. -/
theorem opNorm_adConj_sub_le_two_mul {Y : FiniteModel} {U V : Matrix Y Y ℂ}
    (hU : U ∈ Matrix.unitaryGroup Y ℂ) (hV : V ∈ Matrix.unitaryGroup Y ℂ)
    (X : Matrix Y Y ℂ) :
    ‖adConj U X - adConj V X‖ ≤ 2 * ‖U - V‖ * ‖X‖ := by
  have h := KazhdanAsymptoticCommutant.opNorm_conj_sub_conj_le hU hV
    (le_refl ‖X‖)
  have hcomm : 2 * ‖X‖ * ‖U - V‖ = 2 * ‖U - V‖ * ‖X‖ := by ring
  rw [hcomm] at h
  rw [adConj_apply, adConj_apply]
  exact h

namespace OpAlmostRepresentation

variable {G : Type u} [Group G]

/-! ## The consequence: the conjugation actions are multiplicative mod `c₀` -/

/-- **The conjugation actions of an operator-norm asymptotic representation are
themselves asymptotically multiplicative**, in the operator norm of the matrix
algebra and uniformly in the matrix being conjugated.

This is the printed sentence *"so the operator-norm multiplicative defects of
`(V_n)` also make the conjugation actions multiplicative modulo `c_0`"*, in the
same shape as `OpAlmostRepresentation.asymptoticallyMultiplicative`: the defect
of `g ↦ Ad(V_n(g))` is eventually at most `ε` times the norm of its argument,
so as a sequence of superoperators it is eventually at most `ε` in norm.

The Hilbert--Schmidt counterpart, which is the one the printed ultraproduct
uses, is `OpAlmostRepresentation.adjoint.asymptoticallyMultiplicative`. -/
theorem adConj_asymptoticallyMultiplicative (A : OpAlmostRepresentation G)
    (g h : G) (ε : ℝ) (hε : 0 < ε) :
    ∃ N, ∀ n ≥ N, ∀ X : Matrix (A.model n) (A.model n) ℂ,
      ‖adConj (A.map n (g * h) : Matrix (A.model n) (A.model n) ℂ) X -
          adConj (A.map n g : Matrix (A.model n) (A.model n) ℂ)
            (adConj (A.map n h : Matrix (A.model n) (A.model n) ℂ) X)‖
        ≤ ε * ‖X‖ := by
  obtain ⟨N, hN⟩ := A.asymptoticallyMultiplicative g h (ε / 2) (half_pos hε)
  refine ⟨N, fun n hn X ↦ ?_⟩
  have hcomp : adConj (A.map n g : Matrix (A.model n) (A.model n) ℂ)
        (adConj (A.map n h : Matrix (A.model n) (A.model n) ℂ) X)
      = adConj ((A.map n g : Matrix (A.model n) (A.model n) ℂ) *
          (A.map n h : Matrix (A.model n) (A.model n) ℂ)) X :=
    (adConj_mul _ _ X).symm
  rw [hcomp]
  refine (opNorm_adConj_sub_le_two_mul (A.map n (g * h)).2
    (mul_mem (A.map n g).2 (A.map n h).2) X).trans ?_
  have hdefect := hN n hn
  have hscale : 2 * ‖(A.map n (g * h) : Matrix (A.model n) (A.model n) ℂ) -
      (A.map n g : Matrix (A.model n) (A.model n) ℂ) *
        (A.map n h : Matrix (A.model n) (A.model n) ℂ)‖ ≤ ε := by
    linarith
  exact mul_le_mul_of_nonneg_right hscale (norm_nonneg X)

/-! ## Choosing matrix units -/

/-- **An operator-norm asymptotic representation, read on matrix units.**

Every finite model is replaced by the literal natural basis `Fin (card)` of the
same cardinality.  Nothing analytic happens: the reindexing is a star-algebra
isomorphism preserving the operator norm
(`MatrixReindexHS.norm_naturalize`), so the multiplicative defect is unchanged
coordinate by coordinate.  This is the manuscript's *"after choosing matrix
units on each `M_{d_n}(ℂ)`"*. -/
def naturalizeCoordinates (A : OpAlmostRepresentation G) :
    OpAlmostRepresentation G where
  model n := naturalizedModel A.model n
  modelNonempty n := by
    show 0 < Fintype.card (naturalizedModel A.model n)
    have hcard : Fintype.card (naturalizedModel A.model n)
        = Fintype.card (A.model n) :=
      card_naturalFiniteModel (Fintype.card (A.model n))
    rw [hcard]
    exact A.modelNonempty n
  map n g := naturalizeUnitary A.model A.map n g
  asymptoticallyMultiplicative g h ε hε := by
    obtain ⟨N, hN⟩ := A.asymptoticallyMultiplicative g h ε hε
    refine ⟨N, fun n hn ↦ ?_⟩
    have hrw : (naturalizeUnitary A.model A.map n (g * h) :
          Matrix (naturalizedModel A.model n)
            (naturalizedModel A.model n) ℂ) -
        (naturalizeUnitary A.model A.map n g :
          Matrix (naturalizedModel A.model n)
            (naturalizedModel A.model n) ℂ) *
          naturalizeUnitary A.model A.map n h
        = MatrixReindexHS.naturalize A.model n
            ((A.map n (g * h) : Matrix (A.model n) (A.model n) ℂ) -
              (A.map n g : Matrix (A.model n) (A.model n) ℂ) * A.map n h) := by
      simp only [map_sub, map_mul, coe_naturalizeUnitary]
    -- Stated as a `have` and discharged by `exact`: the structure field's goal
    -- carries `map`/`model` as the applied lambdas of the fields just given,
    -- which `rw` matches only after beta reduction, while `exact` sees through
    -- it definitionally.
    have hfinal : ‖(naturalizeUnitary A.model A.map n (g * h) :
          Matrix (naturalizedModel A.model n)
            (naturalizedModel A.model n) ℂ) -
        (naturalizeUnitary A.model A.map n g :
          Matrix (naturalizedModel A.model n)
            (naturalizedModel A.model n) ℂ) *
          naturalizeUnitary A.model A.map n h‖ ≤ ε := by
      rw [hrw, MatrixReindexHS.norm_naturalize]
      exact hN n hn
    exact hfinal

@[simp] theorem naturalizeCoordinates_model (A : OpAlmostRepresentation G)
    (n : ℕ) :
    A.naturalizeCoordinates.model n = naturalizedModel A.model n := rfl

/-- On matrix units the map is still the same matrix, reindexed. -/
theorem coe_naturalizeCoordinates_map (A : OpAlmostRepresentation G) (n : ℕ)
    (g : G) :
    HEq
      ((A.naturalizeCoordinates.map n g :
          Matrix.unitaryGroup (A.naturalizeCoordinates.model n) ℂ) :
          Matrix (A.naturalizeCoordinates.model n)
            (A.naturalizeCoordinates.model n) ℂ)
      (MatrixReindexHS.naturalize A.model n
        (A.map n g : Matrix (A.model n) (A.model n) ℂ)) := by
  change HEq
    ((naturalizeUnitary A.model A.map n g :
        Matrix.unitaryGroup (naturalizedModel A.model n) ℂ) :
        Matrix (naturalizedModel A.model n)
          (naturalizedModel A.model n) ℂ)
    (MatrixReindexHS.naturalize A.model n
      (A.map n g : Matrix (A.model n) (A.model n) ℂ))
  exact heq_of_eq (coe_naturalizeUnitary A.model A.map n g)

/-! ## The coordinate sizes are `d_n²` -/

/-- **The manuscript's remark, in the form it has content in.**  The adjoint
almost representation `g ↦ Ad(V_n(g))`, read on matrix units, is carried by
matrix coordinates of size exactly `d_n^2`, where `d_n` is the coordinate size
of the original representation.

`OpAlmostRepresentation.adjoint` builds the adjoint over the doubled index
`Y × Y`; `naturalizeCoordinates` chooses matrix units there; and the count is
`card (Y × Y) = (card Y)^2`. -/
theorem card_adjoint_naturalizeCoordinates_model
    (A : OpAlmostRepresentation G) (n : ℕ) :
    Fintype.card (A.adjoint.naturalizeCoordinates.model n)
      = Fintype.card (A.model n) ^ 2 := by
  show Fintype.card
      (naturalFiniteModel (Fintype.card (doubleModel (A.model n)))) = _
  rw [card_naturalFiniteModel, card_doubleModel]
  ring

/-- On matrix units, the adjoint map is still the same matrix, reindexed.  The
matrix itself is `conjDouble (V_n g) = V_n(g) ⊗ conj V_n(g)`, by
`OpAlmostRepresentation.adjoint_map`. -/
theorem coe_adjoint_naturalizeCoordinates_map (A : OpAlmostRepresentation G)
    (n : ℕ) (g : G) :
    HEq
      ((A.adjoint.naturalizeCoordinates.map n g :
          Matrix.unitaryGroup
            (A.adjoint.naturalizeCoordinates.model n) ℂ) :
          Matrix (A.adjoint.naturalizeCoordinates.model n)
            (A.adjoint.naturalizeCoordinates.model n) ℂ)
      (MatrixReindexHS.naturalize A.adjoint.model n
        (A.adjoint.map n g :
          Matrix (A.adjoint.model n) (A.adjoint.model n) ℂ)) := by
  change HEq
    ((naturalizeUnitary A.adjoint.model A.adjoint.map n g :
        Matrix.unitaryGroup (naturalizedModel A.adjoint.model n) ℂ) :
        Matrix (naturalizedModel A.adjoint.model n)
          (naturalizedModel A.adjoint.model n) ℂ)
    (MatrixReindexHS.naturalize A.adjoint.model n
      (A.adjoint.map n g :
        Matrix (A.adjoint.model n) (A.adjoint.model n) ℂ))
  exact heq_of_eq
    (coe_naturalizeUnitary A.adjoint.model A.adjoint.map n g)

/-! ## The two sub-steps, as one statement -/

/-- **The opening paragraph of the printed transport proof, in the matrix-algebra
picture.**  Three conjuncts, one per printed assertion: the displayed estimate,
its consequence for the conjugation actions of an operator-norm asymptotic
representation, and the coordinate count `d_n^2` after matrix units are chosen.

The first conjunct is dimension-free and quantifies over all finite models, so
it is the printed inequality and not an instance of it. -/
theorem printedAdjointParagraph (A : OpAlmostRepresentation G) :
    (∀ (Z : FiniteModel) (U V : Matrix Z Z ℂ),
        U ∈ Matrix.unitaryGroup Z ℂ → V ∈ Matrix.unitaryGroup Z ℂ →
        ∀ X : Matrix Z Z ℂ,
          ‖adConj U X - adConj V X‖ ≤ 2 * ‖U - V‖ * ‖X‖) ∧
      (∀ g h : G, ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
        ∀ X : Matrix (A.model n) (A.model n) ℂ,
          ‖adConj (A.map n (g * h) : Matrix (A.model n) (A.model n) ℂ) X -
              adConj (A.map n g : Matrix (A.model n) (A.model n) ℂ)
                (adConj (A.map n h : Matrix (A.model n) (A.model n) ℂ) X)‖
            ≤ ε * ‖X‖) ∧
      (∀ n : ℕ, Fintype.card (A.adjoint.naturalizeCoordinates.model n)
        = Fintype.card (A.model n) ^ 2) :=
  ⟨fun _ _ _ hU hV X ↦ opNorm_adConj_sub_le_two_mul hU hV X,
    fun g h ε hε ↦ A.adConj_asymptoticallyMultiplicative g h ε hε,
    fun n ↦ A.card_adjoint_naturalizeCoordinates_model n⟩

end OpAlmostRepresentation

end

end GroupApproximation
