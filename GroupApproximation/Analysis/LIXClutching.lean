import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Instances.Matrix
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# The clutching layer for STW Problem LIX

Problem LIX of Schafhauser--Tikuisis--White asks whether every unital simple
`C^*`-algebra is `K_1`-injective.  The counterexample of
`research/artifacts/stw59-simple-ah-k1-counterexample-manuscript-2026-09-05.md`
runs a unitary through a *clutching* construction: a continuous unitary-valued
map on an equator `S^n` is turned into a rank-`k` projection over the sphere
`S^{n+1}` one dimension up, and the two objects are then compared -- a unitary
that is null-homotopic must produce a projection equivalent to the untwisted
one.  This file is that bridge, and it is elementary: no bundle theory, no
Chern classes, no homotopy groups.

## The model

A bundle is a projection-valued map and an isomorphism of bundles is a
Murray--von Neumann equivalence of projections.  The sphere `S^{n+1}` is not
used through any particular coordinate presentation; instead a *suspension
chart* on a space `X` is a pair

* `t : X → ℝ`  (the height, `-1` at the south pole and `1` at the north), and
* `ν : X → E`  (the equatorial part, valued in a real normed space)

with `‖ν x‖² + (t x)² = 1`.  Every model of `S^{n+1}` with a chosen axis
carries one, and nothing below depends on which.

Given a clutching function `w` on the unit sphere of `E`, the clutched
projection is written down by an explicit formula:

```text
clutchMat t f = ⎡ ((1+t)/2)·1     (1/2)·fᴴ ⎤       f = ‖y‖ · w (y/‖y‖)
                ⎣ (1/2)·f       ((1-t)/2)·1 ⎦
```

inside `M_{2k}(ℂ)`.  The single algebraic input is that `f` is `‖y‖` times a
unitary, i.e. `fᴴ f = f fᴴ = (1 - t²)·1` (`IsClutchDatum`); with that,
`clutchMat t f` is a self-adjoint idempotent of trace `k`.  Its continuity at
the two poles -- where the direction `y/‖y‖` has no limit at all -- is bought
by the factor `‖y‖`, and that is the whole content of "the gluing is
continuous".

Taking `k = 1`, `E = ℝ²` and `w` the identity of the unit circle recovers
`(1/2)(1 + x·σ)` over `S²`, the tautological line of `CP¹`; so the formula is
normalised correctly.

## Main results

* `clutchMat_conjTranspose`, `clutchMat_mul_self`, `trace_clutchMat` --
  the clutched matrix is a self-adjoint idempotent of trace `k`.
* `clutchConj_mul_clutchMat_mul_conjTranspose` -- changing `f` by a unitary
  left factor conjugates the clutched projection by `diag(1, h)`.
* `seamMat_conjTranspose_mul_self`, `seamMat_mul_conjTranspose` -- the
  *seam isometry*: an explicit partial isometry implementing a Murray--von
  Neumann equivalence between two clutched projections that share a seam
  datum.  This is the algebraic engine, and it needs no functional calculus,
  no square roots and no polar decomposition.
* `clutchMat_directSum` -- clutching is additive in direct sums.
* `exists_partialIsometry_of_isDiscUnitary` -- **null-homotopy kills the
  twist.**  If the clutching function extends to a continuous unitary-valued
  map on the closed unit ball (which is exactly null-homotopy: a path is
  turned into a disc by collapsing its identity end to the centre), then the
  clutched projection is Murray--von Neumann equivalent to the untwisted one,
  via an explicit continuous partial isometry.

## Why the seam isometry, and not a homotopy argument

The usual route from "the clutching function is null-homotopic" to "the
clutched bundles are isomorphic" runs through *homotopic projections are
unitarily equivalent*, which in a `C^*`-algebra needs the inverse square root
of `1 - (p-q)²` and hence a functional calculus.  The route taken here avoids
that entirely.  Writing `A_f` for the isometry of `ℂ^k` onto the range of
`clutchMat t f` coming from the upper hemisphere trivialisation, the
comparison map is `A_g κ A_fᴴ` for a unitary gauge `κ`; expanded into blocks
that is `seamMat`, whose bottom-right entry has a spurious `1/(1+t)` --
cancelled once and for all against the vanishing of `g κ fᴴ` at the south
pole by carrying the renormalised product `m` as separate data.  The gauge `κ`
is chosen to be the identity at the north pole and to *equal* the clutching
function on a whole collar around the south pole; that plateau, rather than
any uniform-continuity estimate, is what makes `m` continuous there.

## What is not here

Nothing in this file asserts that any particular clutching function fails to
be null-homotopic; that is the hard direction, it is owned by the obstruction
lane, and it is recorded here only as the named proposition
`ClutchingObstruction`.
-/

namespace GroupApproximation
namespace LIX

open scoped Matrix

set_option linter.unusedSectionVars false

noncomputable section

/-! ## The clutched matrix -/

section Algebra

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **The clutched projection.**  `clutchMat t f` is the explicit `2k × 2k`
matrix built from a height `t ∈ [-1,1]` and a matrix `f` which is `‖y‖` times a
unitary.  It is the projection whose range is the fibre of the bundle obtained
by gluing two trivial rank-`k` bundles over the two hemispheres of `S^{n+1}`
along the equator, using `f/‖y‖` as transition function. -/
def clutchMat (t : ℝ) (f : Matrix n n ℂ) :
    Matrix (n ⊕ n) (n ⊕ n) ℂ :=
  Matrix.fromBlocks ((((1 + t) / 2 : ℝ) : ℂ) • (1 : Matrix n n ℂ))
    ((1 / 2 : ℂ) • fᴴ) ((1 / 2 : ℂ) • f)
    ((((1 - t) / 2 : ℝ) : ℂ) • (1 : Matrix n n ℂ))

/-- The algebraic condition making `clutchMat t f` a projection: `f` is `‖y‖`
times a unitary, where `‖y‖² = 1 - t²`. -/
def IsClutchDatum (t : ℝ) (f : Matrix n n ℂ) : Prop :=
  fᴴ * f = (1 - (t : ℂ) ^ 2) • (1 : Matrix n n ℂ) ∧
    f * fᴴ = (1 - (t : ℂ) ^ 2) • (1 : Matrix n n ℂ)

/-- Scalars pull out of a product of matrices. -/
private theorem smul_mul_smul_matrix (a b : ℂ) (M N : Matrix n n ℂ) :
    (a • M) * (b • N) = (a * b) • (M * N) := by
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]

private theorem star_ofReal_complex (r : ℝ) : star ((r : ℝ) : ℂ) = ((r : ℝ) : ℂ) := by
  simp [Complex.conj_ofReal]

/-- The clutched matrix is self-adjoint. -/
theorem clutchMat_conjTranspose (t : ℝ) (f : Matrix n n ℂ) :
    (clutchMat t f)ᴴ = clutchMat t f := by
  rw [clutchMat, Matrix.fromBlocks_conjTranspose]
  simp [Matrix.conjTranspose_smul, Complex.conj_ofReal]

/-- The clutched matrix is idempotent. -/
theorem clutchMat_mul_self {t : ℝ} {f : Matrix n n ℂ} (hf : IsClutchDatum t f) :
    clutchMat t f * clutchMat t f = clutchMat t f := by
  obtain ⟨hf1, hf2⟩ := hf
  rw [clutchMat, Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have e1 : ((((1 + t) / 2 : ℝ) : ℂ) • (1 : Matrix n n ℂ)) *
        ((((1 + t) / 2 : ℝ) : ℂ) • (1 : Matrix n n ℂ))
        = ((((1 + t) / 2 : ℝ) : ℂ) * (((1 + t) / 2 : ℝ) : ℂ)) •
          (1 : Matrix n n ℂ) := by
      rw [smul_mul_smul_matrix, Matrix.one_mul]
    have e2 : ((1 / 2 : ℂ) • fᴴ) * ((1 / 2 : ℂ) • f)
        = ((1 / 2 : ℂ) * (1 / 2 : ℂ) * (1 - (t : ℂ) ^ 2)) • (1 : Matrix n n ℂ) := by
      rw [smul_mul_smul_matrix, hf1, smul_smul, mul_assoc]
    rw [e1, e2, ← add_smul]
    congr 1
    push_cast
    ring
  · have e1 : ((((1 + t) / 2 : ℝ) : ℂ) • (1 : Matrix n n ℂ)) * ((1 / 2 : ℂ) • fᴴ)
        = ((((1 + t) / 2 : ℝ) : ℂ) * (1 / 2 : ℂ)) • fᴴ := by
      rw [smul_mul_smul_matrix, Matrix.one_mul]
    have e2 : ((1 / 2 : ℂ) • fᴴ) * ((((1 - t) / 2 : ℝ) : ℂ) • (1 : Matrix n n ℂ))
        = ((1 / 2 : ℂ) * (((1 - t) / 2 : ℝ) : ℂ)) • fᴴ := by
      rw [smul_mul_smul_matrix, Matrix.mul_one]
    rw [e1, e2, ← add_smul]
    congr 1
    push_cast
    ring
  · have e1 : ((1 / 2 : ℂ) • f) * ((((1 + t) / 2 : ℝ) : ℂ) • (1 : Matrix n n ℂ))
        = ((1 / 2 : ℂ) * (((1 + t) / 2 : ℝ) : ℂ)) • f := by
      rw [smul_mul_smul_matrix, Matrix.mul_one]
    have e2 : ((((1 - t) / 2 : ℝ) : ℂ) • (1 : Matrix n n ℂ)) * ((1 / 2 : ℂ) • f)
        = ((((1 - t) / 2 : ℝ) : ℂ) * (1 / 2 : ℂ)) • f := by
      rw [smul_mul_smul_matrix, Matrix.one_mul]
    rw [e1, e2, ← add_smul]
    congr 1
    push_cast
    ring
  · have e1 : ((1 / 2 : ℂ) • f) * ((1 / 2 : ℂ) • fᴴ)
        = ((1 / 2 : ℂ) * (1 / 2 : ℂ) * (1 - (t : ℂ) ^ 2)) • (1 : Matrix n n ℂ) := by
      rw [smul_mul_smul_matrix, hf2, smul_smul, mul_assoc]
    have e2 : ((((1 - t) / 2 : ℝ) : ℂ) • (1 : Matrix n n ℂ)) *
        ((((1 - t) / 2 : ℝ) : ℂ) • (1 : Matrix n n ℂ))
        = ((((1 - t) / 2 : ℝ) : ℂ) * (((1 - t) / 2 : ℝ) : ℂ)) •
          (1 : Matrix n n ℂ) := by
      rw [smul_mul_smul_matrix, Matrix.one_mul]
    rw [e1, e2, ← add_smul]
    congr 1
    push_cast
    ring

/-- The clutched matrix has trace `k`: the glued bundle has rank `k`. -/
theorem trace_clutchMat (t : ℝ) (f : Matrix n n ℂ) :
    (clutchMat t f).trace = (Fintype.card n : ℂ) := by
  have hsum : (clutchMat t f).trace
      = (∑ _i : n, (((1 + t) / 2 : ℝ) : ℂ)) + ∑ _i : n, (((1 - t) / 2 : ℝ) : ℂ) := by
    show (∑ i : n ⊕ n, clutchMat t f i i) = _
    rw [Fintype.sum_sum_type]
    congr 1
    · exact Finset.sum_congr rfl fun i _ => by
        simp [clutchMat, Matrix.one_apply_eq]
    · exact Finset.sum_congr rfl fun i _ => by
        simp [clutchMat, Matrix.one_apply_eq]
  rw [hsum]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  push_cast
  ring

/-- The block-diagonal unitary `diag(1, h)` used to change a hemisphere
trivialisation. -/
def clutchConj (h : Matrix n n ℂ) : Matrix (n ⊕ n) (n ⊕ n) ℂ :=
  Matrix.fromBlocks 1 0 0 h

theorem clutchConj_conjTranspose (h : Matrix n n ℂ) :
    (clutchConj h)ᴴ = clutchConj hᴴ := by
  rw [clutchConj, clutchConj, Matrix.fromBlocks_conjTranspose]
  simp

theorem clutchConj_conjTranspose_mul_self {h : Matrix n n ℂ} (hh : hᴴ * h = 1) :
    (clutchConj h)ᴴ * clutchConj h = 1 := by
  rw [clutchConj_conjTranspose, clutchConj, clutchConj, Matrix.fromBlocks_multiply, hh]
  simp

theorem clutchConj_mul_conjTranspose_self {h : Matrix n n ℂ} (hh : h * hᴴ = 1) :
    clutchConj h * (clutchConj h)ᴴ = 1 := by
  rw [clutchConj_conjTranspose, clutchConj, clutchConj, Matrix.fromBlocks_multiply, hh]
  simp

/-- **Changing a hemisphere trivialisation.**  Multiplying the clutching datum
on the left by a unitary `h` conjugates the clutched projection by
`diag(1, h)`. -/
theorem clutchConj_mul_clutchMat_mul_conjTranspose (t : ℝ) {h g : Matrix n n ℂ}
    (hh : h * hᴴ = 1) :
    clutchConj h * clutchMat t g * (clutchConj h)ᴴ = clutchMat t (h * g) := by
  rw [clutchConj_conjTranspose, clutchConj, clutchConj, clutchMat, clutchMat,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp
  · simp
  · simp
  · simp [hh]

/-! ## The seam isometry -/

/-- The seam isometry.  `κ` is the unitary re-gauging the seam; `m` is the
renormalised product `g κ fᴴ / (1 - t²)`, supplied separately precisely so
that the formula stays regular at the south pole. -/
def seamMat (t : ℝ) (f g κ m : Matrix n n ℂ) :
    Matrix (n ⊕ n) (n ⊕ n) ℂ :=
  Matrix.fromBlocks ((((1 + t) / 2 : ℝ) : ℂ) • κ) ((1 / 2 : ℂ) • (κ * fᴴ))
    ((1 / 2 : ℂ) • (g * κ)) ((((1 - t) / 2 : ℝ) : ℂ) • m)

theorem seamMat_conjTranspose (t : ℝ) (f g κ m : Matrix n n ℂ) :
    (seamMat t f g κ m)ᴴ =
      Matrix.fromBlocks ((((1 + t) / 2 : ℝ) : ℂ) • κᴴ) ((1 / 2 : ℂ) • (κᴴ * gᴴ))
        ((1 / 2 : ℂ) • (f * κᴴ)) ((((1 - t) / 2 : ℝ) : ℂ) • mᴴ) := by
  rw [seamMat, Matrix.fromBlocks_conjTranspose]
  simp [Matrix.conjTranspose_smul, Complex.conj_ofReal]

/-- The seam isometry is a partial isometry with initial projection the
clutched projection of `f`. -/
theorem seamMat_conjTranspose_mul_self {t : ℝ} {f g κ m : Matrix n n ℂ}
    (hf : IsClutchDatum t f) (hg : IsClutchDatum t g)
    (hκ : κᴴ * κ = 1) (hm : mᴴ * m = 1)
    (hseam : κᴴ * gᴴ * m = fᴴ) :
    (seamMat t f g κ m)ᴴ * seamMat t f g κ m = clutchMat t f := by
  obtain ⟨hf1, hf2⟩ := hf
  obtain ⟨hg1, hg2⟩ := hg
  have hseam' : mᴴ * g * κ = f := by
    have h := congrArg Matrix.conjTranspose hseam
    simpa [Matrix.conjTranspose_mul, Matrix.mul_assoc] using h
  rw [seamMat_conjTranspose, seamMat, Matrix.fromBlocks_multiply, clutchMat,
    Matrix.fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have e1 : ((((1 + t) / 2 : ℝ) : ℂ) • κᴴ) * ((((1 + t) / 2 : ℝ) : ℂ) • κ)
        = ((((1 + t) / 2 : ℝ) : ℂ) * (((1 + t) / 2 : ℝ) : ℂ)) •
            (1 : Matrix n n ℂ) := by
      rw [smul_mul_smul_matrix, hκ]
    have e2 : ((1 / 2 : ℂ) • (κᴴ * gᴴ)) * ((1 / 2 : ℂ) • (g * κ))
        = ((1 / 2 : ℂ) * (1 / 2 : ℂ) * (1 - (t : ℂ) ^ 2)) •
            (1 : Matrix n n ℂ) := by
      have hinner : (κᴴ * gᴴ) * (g * κ) = (1 - (t : ℂ) ^ 2) • (1 : Matrix n n ℂ) := by
        rw [Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, hg1, Matrix.smul_mul, Matrix.mul_smul,
          Matrix.one_mul, hκ]
      rw [smul_mul_smul_matrix, hinner, smul_smul, mul_assoc]
    rw [e1, e2, ← add_smul]
    congr 1
    push_cast
    ring
  · have e1 : ((((1 + t) / 2 : ℝ) : ℂ) • κᴴ) * ((1 / 2 : ℂ) • (κ * fᴴ))
        = ((((1 + t) / 2 : ℝ) : ℂ) * (1 / 2 : ℂ)) • fᴴ := by
      rw [smul_mul_smul_matrix, ← Matrix.mul_assoc, hκ, Matrix.one_mul]
    have e2 : ((1 / 2 : ℂ) • (κᴴ * gᴴ)) * ((((1 - t) / 2 : ℝ) : ℂ) • m)
        = ((1 / 2 : ℂ) * (((1 - t) / 2 : ℝ) : ℂ)) • fᴴ := by
      rw [smul_mul_smul_matrix, hseam]
    rw [e1, e2, ← add_smul]
    congr 1
    push_cast
    ring
  · have e1 : ((1 / 2 : ℂ) • (f * κᴴ)) * ((((1 + t) / 2 : ℝ) : ℂ) • κ)
        = ((1 / 2 : ℂ) * (((1 + t) / 2 : ℝ) : ℂ)) • f := by
      rw [smul_mul_smul_matrix, Matrix.mul_assoc, hκ, Matrix.mul_one]
    have e2 : ((((1 - t) / 2 : ℝ) : ℂ) • mᴴ) * ((1 / 2 : ℂ) • (g * κ))
        = ((((1 - t) / 2 : ℝ) : ℂ) * (1 / 2 : ℂ)) • f := by
      rw [smul_mul_smul_matrix, ← Matrix.mul_assoc, hseam']
    rw [e1, e2, ← add_smul]
    congr 1
    push_cast
    ring
  · have e1 : ((1 / 2 : ℂ) • (f * κᴴ)) * ((1 / 2 : ℂ) • (κ * fᴴ))
        = ((1 / 2 : ℂ) * (1 / 2 : ℂ) * (1 - (t : ℂ) ^ 2)) •
            (1 : Matrix n n ℂ) := by
      have hinner : (f * κᴴ) * (κ * fᴴ) = (1 - (t : ℂ) ^ 2) • (1 : Matrix n n ℂ) := by
        rw [Matrix.mul_assoc, ← Matrix.mul_assoc κᴴ, hκ, Matrix.one_mul, hf2]
      rw [smul_mul_smul_matrix, hinner, smul_smul, mul_assoc]
    have e2 : ((((1 - t) / 2 : ℝ) : ℂ) • mᴴ) * ((((1 - t) / 2 : ℝ) : ℂ) • m)
        = ((((1 - t) / 2 : ℝ) : ℂ) * (((1 - t) / 2 : ℝ) : ℂ)) •
            (1 : Matrix n n ℂ) := by
      rw [smul_mul_smul_matrix, hm]
    rw [e1, e2, ← add_smul]
    congr 1
    push_cast
    ring

/-- The seam isometry is a partial isometry with final projection the clutched
projection of `g`. -/
theorem seamMat_mul_conjTranspose {t : ℝ} {f g κ m : Matrix n n ℂ}
    (hf : IsClutchDatum t f) (hg : IsClutchDatum t g)
    (hκ : κ * κᴴ = 1) (hm : m * mᴴ = 1)
    (hseam : κᴴ * gᴴ * m = fᴴ) :
    seamMat t f g κ m * (seamMat t f g κ m)ᴴ = clutchMat t g := by
  obtain ⟨hf1, hf2⟩ := hf
  obtain ⟨hg1, hg2⟩ := hg
  have hgstar : κ * fᴴ * mᴴ = gᴴ := by
    have h : κ * (κᴴ * gᴴ * m) * mᴴ = κ * fᴴ * mᴴ := by rw [hseam]
    rw [← h]
    simp only [← Matrix.mul_assoc]
    rw [hκ, Matrix.one_mul, Matrix.mul_assoc, hm, Matrix.mul_one]
  have hgstar' : m * f * κᴴ = g := by
    have h := congrArg Matrix.conjTranspose hgstar
    simpa [Matrix.conjTranspose_mul, Matrix.mul_assoc] using h
  rw [seamMat_conjTranspose, seamMat, Matrix.fromBlocks_multiply, clutchMat,
    Matrix.fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have e1 : ((((1 + t) / 2 : ℝ) : ℂ) • κ) * ((((1 + t) / 2 : ℝ) : ℂ) • κᴴ)
        = ((((1 + t) / 2 : ℝ) : ℂ) * (((1 + t) / 2 : ℝ) : ℂ)) •
            (1 : Matrix n n ℂ) := by
      rw [smul_mul_smul_matrix, hκ]
    have e2 : ((1 / 2 : ℂ) • (κ * fᴴ)) * ((1 / 2 : ℂ) • (f * κᴴ))
        = ((1 / 2 : ℂ) * (1 / 2 : ℂ) * (1 - (t : ℂ) ^ 2)) •
            (1 : Matrix n n ℂ) := by
      have hinner : (κ * fᴴ) * (f * κᴴ) = (1 - (t : ℂ) ^ 2) • (1 : Matrix n n ℂ) := by
        rw [Matrix.mul_assoc, ← Matrix.mul_assoc fᴴ, hf1, Matrix.smul_mul, Matrix.mul_smul,
          Matrix.one_mul, hκ]
      rw [smul_mul_smul_matrix, hinner, smul_smul, mul_assoc]
    rw [e1, e2, ← add_smul]
    congr 1
    push_cast
    ring
  · have e1 : ((((1 + t) / 2 : ℝ) : ℂ) • κ) * ((1 / 2 : ℂ) • (κᴴ * gᴴ))
        = ((((1 + t) / 2 : ℝ) : ℂ) * (1 / 2 : ℂ)) • gᴴ := by
      rw [smul_mul_smul_matrix, ← Matrix.mul_assoc, hκ, Matrix.one_mul]
    have e2 : ((1 / 2 : ℂ) • (κ * fᴴ)) * ((((1 - t) / 2 : ℝ) : ℂ) • mᴴ)
        = ((1 / 2 : ℂ) * (((1 - t) / 2 : ℝ) : ℂ)) • gᴴ := by
      rw [smul_mul_smul_matrix, hgstar]
    rw [e1, e2, ← add_smul]
    congr 1
    push_cast
    ring
  · have e1 : ((1 / 2 : ℂ) • (g * κ)) * ((((1 + t) / 2 : ℝ) : ℂ) • κᴴ)
        = ((1 / 2 : ℂ) * (((1 + t) / 2 : ℝ) : ℂ)) • g := by
      rw [smul_mul_smul_matrix, Matrix.mul_assoc, hκ, Matrix.mul_one]
    have e2 : ((((1 - t) / 2 : ℝ) : ℂ) • m) * ((1 / 2 : ℂ) • (f * κᴴ))
        = ((((1 - t) / 2 : ℝ) : ℂ) * (1 / 2 : ℂ)) • g := by
      rw [smul_mul_smul_matrix, ← Matrix.mul_assoc, hgstar']
    rw [e1, e2, ← add_smul]
    congr 1
    push_cast
    ring
  · have e1 : ((1 / 2 : ℂ) • (g * κ)) * ((1 / 2 : ℂ) • (κᴴ * gᴴ))
        = ((1 / 2 : ℂ) * (1 / 2 : ℂ) * (1 - (t : ℂ) ^ 2)) •
            (1 : Matrix n n ℂ) := by
      have hinner : (g * κ) * (κᴴ * gᴴ) = (1 - (t : ℂ) ^ 2) • (1 : Matrix n n ℂ) := by
        rw [Matrix.mul_assoc, ← Matrix.mul_assoc κ, hκ, Matrix.one_mul, hg2]
      rw [smul_mul_smul_matrix, hinner, smul_smul, mul_assoc]
    have e2 : ((((1 - t) / 2 : ℝ) : ℂ) • m) * ((((1 - t) / 2 : ℝ) : ℂ) • mᴴ)
        = ((((1 - t) / 2 : ℝ) : ℂ) * (((1 - t) / 2 : ℝ) : ℂ)) •
            (1 : Matrix n n ℂ) := by
      rw [smul_mul_smul_matrix, hm]
    rw [e1, e2, ← add_smul]
    congr 1
    push_cast
    ring

/-- Products of unitaries are unitary. -/
theorem unitary_mul_unitary {A B : Matrix n n ℂ}
    (hA : Aᴴ * A = 1) (hA' : A * Aᴴ = 1) (hB : Bᴴ * B = 1) (hB' : B * Bᴴ = 1) :
    (A * B)ᴴ * (A * B) = 1 ∧ (A * B) * (A * B)ᴴ = 1 := by
  constructor
  · rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Aᴴ, hA, Matrix.one_mul, hB]
  · rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc B, hB', Matrix.one_mul, hA']

/-! ## Direct sums -/

/-- **Clutching is additive.**  The clutched projection of a block-diagonal
clutching datum is, after the obvious reindexing of `ℂ^{2(k₁+k₂)}`, the direct
sum of the two clutched projections.  Applied with `f₂` the untwisted datum
`‖y‖·1`, this says that `clutch (w ⊕ 1_H)` is `clutch w ⊕ (pullback of H)`,
which is how the manuscript's comparison unitary `w = u ⊕ 1_H` is fed into the
obstruction. -/
theorem clutchMat_directSum {n₁ n₂ : Type*} [Fintype n₁] [DecidableEq n₁] [Fintype n₂]
    [DecidableEq n₂] (t : ℝ) (f₁ : Matrix n₁ n₁ ℂ) (f₂ : Matrix n₂ n₂ ℂ) :
    (clutchMat t (Matrix.fromBlocks f₁ 0 0 f₂)).submatrix
        ⇑(Equiv.sumSumSumComm n₁ n₁ n₂ n₂) ⇑(Equiv.sumSumSumComm n₁ n₁ n₂ n₂)
      = Matrix.fromBlocks (clutchMat t f₁) 0 0 (clutchMat t f₂) := by
  ext i j
  rcases i with (i | i) | (i | i) <;> rcases j with (j | j) | (j | j) <;>
    simp [clutchMat, Equiv.sumSumSumComm, Matrix.one_apply]

end Algebra

/-! ## Continuity toolkit -/

section Continuity

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Every entry of a unitary matrix has modulus at most one. -/
theorem norm_entry_le_one {A : Matrix n n ℂ} (hA : Aᴴ * A = 1) (i j : n) :
    ‖A i j‖ ≤ 1 := by
  have hjj : ∑ l : n, ((‖A l j‖ ^ 2 : ℝ) : ℂ) = 1 := by
    have h := congrArg (fun M : Matrix n n ℂ => M j j) hA
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq] at h
    rw [← h]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← starRingEnd_apply, RCLike.conj_mul]
    norm_cast
  have hreal : ∑ l : n, ‖A l j‖ ^ 2 = 1 := by
    have hc : ((∑ l : n, ‖A l j‖ ^ 2 : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
      push_cast
      simpa using hjj
    exact_mod_cast hc
  have hle : ‖A i j‖ ^ 2 ≤ 1 := by
    rw [← hreal]
    exact Finset.single_le_sum (fun l _ => sq_nonneg (‖A l j‖)) (Finset.mem_univ i)
  nlinarith [norm_nonneg (A i j)]

/-- **Damped continuity.**  A uniformly bounded matrix field that is
continuous on an open set `U`, scaled by a continuous real function vanishing
off `U`, is globally continuous.  This is the mechanism by which the clutched
projection survives the poles, where the equatorial direction has no limit. -/
theorem continuous_damped {X : Type*} [TopologicalSpace X] {U : Set X} (hU : IsOpen U)
    {r : X → ℝ} (hr : Continuous r) {F : X → Matrix n n ℂ}
    (hF : ContinuousOn F U) (hb : ∀ x i j, ‖F x i j‖ ≤ 1) (h0 : ∀ x, x ∉ U → r x = 0) :
    Continuous fun x => ((r x : ℝ) : ℂ) • F x := by
  refine continuous_matrix fun i j => ?_
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [continuous_iff_continuousAt]
  intro x₀
  by_cases hx : x₀ ∈ U
  · have hFc : ContinuousAt F x₀ := hF.continuousAt (hU.mem_nhds hx)
    have hent : ContinuousAt (fun x => F x i j) x₀ :=
      (continuous_apply_apply i j).continuousAt.comp hFc
    exact (Complex.continuous_ofReal.continuousAt.comp hr.continuousAt).mul hent
  · have hr0 : r x₀ = 0 := h0 x₀ hx
    have hz : Filter.Tendsto (fun x => ((r x : ℝ) : ℂ) * F x i j) (nhds x₀) (nhds 0) := by
      refine squeeze_zero_norm (a := fun x => |r x|) (fun x => ?_) ?_
      · have h1 : ‖((r x : ℝ) : ℂ) * F x i j‖ = ‖((r x : ℝ) : ℂ)‖ * ‖F x i j‖ := norm_mul _ _
        have h2 : ‖((r x : ℝ) : ℂ)‖ = |r x| := by simp
        rw [h1, h2]
        nlinarith [hb x i j, abs_nonneg (r x), norm_nonneg (F x i j)]
      · have h3 : Filter.Tendsto (fun x => |r x|) (nhds x₀) (nhds |r x₀|) :=
          (hr.abs).continuousAt
        rwa [hr0, abs_zero] at h3
    have hval : ((r x₀ : ℝ) : ℂ) * F x₀ i j = 0 := by rw [hr0]; simp
    rw [ContinuousAt, hval]
    exact hz

/-- A vector field dominated in norm by a function tending to zero, and
vanishing at the limit point, is continuous there. -/
theorem continuousAt_of_norm_le {X : Type*} [TopologicalSpace X] {V : Type*}
    [NormedAddCommGroup V] {G : X → V} {r : X → ℝ} {x₀ : X} (hb : ∀ x, ‖G x‖ ≤ r x)
    (hr : Filter.Tendsto r (nhds x₀) (nhds 0)) (h0 : G x₀ = 0) : ContinuousAt G x₀ := by
  rw [ContinuousAt, h0]
  exact squeeze_zero_norm hb hr

/-- Continuity of a `2×2` block matrix from continuity of its blocks. -/
theorem continuous_fromBlocks {X : Type*} [TopologicalSpace X]
    {A B C D : X → Matrix n n ℂ} (hA : Continuous A) (hB : Continuous B)
    (hC : Continuous C) (hD : Continuous D) :
    Continuous fun x => Matrix.fromBlocks (A x) (B x) (C x) (D x) := by
  refine continuous_matrix fun i j => ?_
  rcases i with i | i <;> rcases j with j | j <;>
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂]
  exacts [hA.matrix_elem i j, hB.matrix_elem i j, hC.matrix_elem i j, hD.matrix_elem i j]

theorem continuous_clutchConj {X : Type*} [TopologicalSpace X]
    {h : X → Matrix n n ℂ} (hh : Continuous h) :
    Continuous fun x => clutchConj (h x) :=
  continuous_fromBlocks continuous_const continuous_const continuous_const hh

end Continuity

/-! ## Null-homotopy kills the twist -/

section NullHomotopy

variable {X : Type*} [TopologicalSpace X] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace ℝ E] {n : Type*} [Fintype n] [DecidableEq n]

/-- A **suspension chart**: a height function and an equatorial part obeying
the sphere relation.  Any presentation of `S^{n+1}` with a chosen axis gives
one, and the clutching layer is stated for all of them at once. -/
structure IsSuspensionChart (t : X → ℝ) (ν : X → E) : Prop where
  continuous_height : Continuous t
  continuous_equator : Continuous ν
  sphere : ∀ x, ‖ν x‖ ^ 2 + t x ^ 2 = 1

/-- A **disc unitary**: a continuous unitary-valued map on the closed unit
ball of `E` which is the identity at the centre.  Its restriction to the unit
sphere is a clutching function, and possessing such an extension is exactly
null-homotopy of that clutching function: a norm-continuous path from `w` to
`1` becomes a map on the disc by reading the path parameter off the radius,
its identity end collapsing to the centre. -/
structure IsDiscUnitary (Ω : E → Matrix n n ℂ) : Prop where
  continuous : Continuous Ω
  map_zero : Ω 0 = 1
  star_mul_self : ∀ y : E, ‖y‖ ≤ 1 → (Ω y)ᴴ * Ω y = 1
  mul_star_self : ∀ y : E, ‖y‖ ≤ 1 → Ω y * (Ω y)ᴴ = 1

/-- The **cone** of a clutching function: `y ↦ ‖y‖ · w (y/‖y‖)`.  At the
origin the scalar factor already vanishes, so no case split is needed; and
that factor is exactly what makes the cone continuous there, since the
direction `y/‖y‖` has no limit. -/
def coneMat (Ω : E → Matrix n n ℂ) (y : E) : Matrix n n ℂ :=
  ((‖y‖ : ℝ) : ℂ) • Ω ((‖y‖)⁻¹ • y)

/-- The equatorial direction, `0` at the poles. -/
def chartDir (ν : X → E) (x : X) : E := (‖ν x‖)⁻¹ • ν x

/-- The interpolation used to slide the seam gauge from the identity at the
north pole to the full clutching function on a collar around the south pole.
It is `0` at `t = 1` and `1` for `t ≤ -1/2`; the plateau near the south pole
is what makes the seam correction continuous there. -/
def seamParam (t : ℝ) : ℝ := min 1 (max 0 ((1 - t) * (2 / 3)))

/-- The point of the closed unit ball at which the seam gauge is read off. -/
def seamPoint (t : X → ℝ) (ν : X → E) (x : X) : E :=
  (seamParam (t x) * (‖ν x‖)⁻¹) • ν x

/-- The seam gauge `κ`. -/
def seamGauge (t : X → ℝ) (ν : X → E) (Ω : E → Matrix n n ℂ) (x : X) :
    Matrix n n ℂ := Ω (seamPoint t ν x)

/-- The twisted clutching datum `g = ‖ν‖ · Ω(ν)`: the cone taken along the
radius rather than at the boundary.  It is the intermediate object between the
clutched projection and the untwisted one. -/
def twistedCone (ν : X → E) (Ω : E → Matrix n n ℂ) (x : X) :
    Matrix n n ℂ := ((‖ν x‖ : ℝ) : ℂ) • Ω (ν x)

/-- The seam correction `m`: the renormalised product `g κ fᴴ / (1 - t²)`. -/
def seamCorrection (t : X → ℝ) (ν : X → E) (Ω : E → Matrix n n ℂ) (x : X) :
    Matrix n n ℂ :=
  Ω (ν x) * Ω (seamPoint t ν x) * (Ω (chartDir ν x))ᴴ

theorem coneMat_def (Ω : E → Matrix n n ℂ) (y : E) :
    coneMat Ω y = ((‖y‖ : ℝ) : ℂ) • Ω ((‖y‖)⁻¹ • y) := rfl

theorem chartDir_def (ν : X → E) (x : X) : chartDir ν x = (‖ν x‖)⁻¹ • ν x := rfl

theorem coneMat_apply_equator (Ω : E → Matrix n n ℂ) (ν : X → E) (x : X) :
    coneMat Ω (ν x) = ((‖ν x‖ : ℝ) : ℂ) • Ω (chartDir ν x) := rfl

theorem seamPoint_def (t : X → ℝ) (ν : X → E) (x : X) :
    seamPoint t ν x = (seamParam (t x) * (‖ν x‖)⁻¹) • ν x := rfl

theorem seamGauge_def (t : X → ℝ) (ν : X → E) (Ω : E → Matrix n n ℂ) (x : X) :
    seamGauge t ν Ω x = Ω (seamPoint t ν x) := rfl

theorem twistedCone_def (ν : X → E) (Ω : E → Matrix n n ℂ) (x : X) :
    twistedCone ν Ω x = ((‖ν x‖ : ℝ) : ℂ) • Ω (ν x) := rfl

theorem seamCorrection_def (t : X → ℝ) (ν : X → E) (Ω : E → Matrix n n ℂ) (x : X) :
    seamCorrection t ν Ω x = Ω (ν x) * Ω (seamPoint t ν x) * (Ω (chartDir ν x))ᴴ := rfl

theorem seamParam_nonneg (t : ℝ) : 0 ≤ seamParam t :=
  le_min (by norm_num) (le_max_left _ _)

theorem seamParam_le_one (t : ℝ) : seamParam t ≤ 1 := min_le_left _ _

theorem seamParam_one : seamParam 1 = 0 := by
  simp [seamParam]

theorem seamParam_of_le {t : ℝ} (ht : t ≤ -(1 / 2)) : seamParam t = 1 := by
  have h : (1 : ℝ) ≤ (1 - t) * (2 / 3) := by nlinarith
  exact min_eq_left (le_max_of_le_right h)

theorem continuous_seamParam : Continuous seamParam :=
  continuous_const.min (continuous_const.max
    ((continuous_const.sub continuous_id).mul continuous_const))

theorem norm_chartDir_le_one (ν : X → E) (x : X) : ‖chartDir ν x‖ ≤ 1 := by
  rcases eq_or_ne (ν x) 0 with h | h
  · simp [chartDir_def, h]
  · rw [chartDir_def, norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr h)]

theorem norm_dir_le_one (y : E) : ‖(‖y‖)⁻¹ • y‖ ≤ 1 := by
  rcases eq_or_ne y 0 with h | h
  · simp [h]
  · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr h)]

theorem norm_seamPoint_le (t : X → ℝ) (ν : X → E) (x : X) :
    ‖seamPoint t ν x‖ ≤ seamParam (t x) := by
  rcases eq_or_ne (ν x) 0 with h | h
  · simp [seamPoint_def, h, seamParam_nonneg]
  · rw [seamPoint_def, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (seamParam_nonneg _) (inv_nonneg.mpr (norm_nonneg _))),
      mul_assoc, inv_mul_cancel₀ (norm_ne_zero_iff.mpr h), mul_one]

theorem norm_seamPoint_le_one (t : X → ℝ) (ν : X → E) (x : X) : ‖seamPoint t ν x‖ ≤ 1 :=
  (norm_seamPoint_le t ν x).trans (seamParam_le_one _)

variable {t : X → ℝ} {ν : X → E} {Ω : E → Matrix n n ℂ}

theorem norm_equator_le_one (hc : IsSuspensionChart t ν) (x : X) : ‖ν x‖ ≤ 1 := by
  have h := hc.sphere x
  nlinarith [norm_nonneg (ν x), sq_nonneg (t x)]

theorem height_eq_of_equator_zero (hc : IsSuspensionChart t ν) {x : X} (hx : ν x = 0) :
    t x = 1 ∨ t x = -1 := by
  have hsq : t x ^ 2 = 1 := by
    have h := hc.sphere x
    rw [hx] at h
    simpa using h
  have h2 : (t x - 1) * (t x + 1) = 0 := by
    have hr : (t x - 1) * (t x + 1) = t x ^ 2 - 1 := by ring
    rw [hr, hsq]
    ring
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact Or.inl (by linarith)
  · exact Or.inr (by linarith)

theorem isOpen_equator_ne (hc : IsSuspensionChart t ν) : IsOpen {x : X | ν x ≠ 0} :=
  isOpen_compl_singleton.preimage hc.continuous_equator

/-- The cone of a disc unitary is a clutching datum. -/
theorem isClutchDatum_coneMat (hΩ : IsDiscUnitary Ω) {y : E} {s : ℝ}
    (hy : ‖y‖ ^ 2 + s ^ 2 = 1) : IsClutchDatum s (coneMat Ω y) := by
  have hcast : ((‖y‖ : ℝ) : ℂ) * ((‖y‖ : ℝ) : ℂ) = 1 - (s : ℂ) ^ 2 := by
    have hr : ‖y‖ * ‖y‖ = 1 - s ^ 2 := by nlinarith [hy]
    have := congrArg (fun r : ℝ => ((r : ℝ) : ℂ)) hr
    push_cast at this
    exact this
  have hdle : ‖(‖y‖)⁻¹ • y‖ ≤ 1 := norm_dir_le_one y
  constructor
  · rw [coneMat_def, Matrix.conjTranspose_smul, star_ofReal_complex, Matrix.smul_mul,
      Matrix.mul_smul, hΩ.star_mul_self _ hdle, smul_smul, hcast]
  · rw [coneMat_def, Matrix.conjTranspose_smul, star_ofReal_complex, Matrix.smul_mul,
      Matrix.mul_smul, hΩ.mul_star_self _ hdle, smul_smul, hcast]

/-- The twisted cone is a clutching datum too. -/
theorem isClutchDatum_twistedCone (hc : IsSuspensionChart t ν) (hΩ : IsDiscUnitary Ω) (x : X) :
    IsClutchDatum (t x) (twistedCone ν Ω x) := by
  have hy := hc.sphere x
  have hcast : ((‖ν x‖ : ℝ) : ℂ) * ((‖ν x‖ : ℝ) : ℂ) = 1 - ((t x : ℝ) : ℂ) ^ 2 := by
    have hr : ‖ν x‖ * ‖ν x‖ = 1 - t x ^ 2 := by nlinarith [hy]
    have := congrArg (fun r : ℝ => ((r : ℝ) : ℂ)) hr
    push_cast at this
    exact this
  have hle : ‖ν x‖ ≤ 1 := norm_equator_le_one hc x
  constructor
  · rw [twistedCone_def, Matrix.conjTranspose_smul, star_ofReal_complex, Matrix.smul_mul,
      Matrix.mul_smul, hΩ.star_mul_self _ hle, smul_smul, hcast]
  · rw [twistedCone_def, Matrix.conjTranspose_smul, star_ofReal_complex, Matrix.smul_mul,
      Matrix.mul_smul, hΩ.mul_star_self _ hle, smul_smul, hcast]

/-- The seam identity `κᴴ gᴴ m = fᴴ`, the single relation binding the four
ingredients of the seam isometry.  It holds at every point, including both
poles, with no case split: the products of `Ω`-values telescope. -/
theorem seam_identity (hc : IsSuspensionChart t ν) (hΩ : IsDiscUnitary Ω) (x : X) :
    (seamGauge t ν Ω x)ᴴ * (twistedCone ν Ω x)ᴴ * seamCorrection t ν Ω x
      = (coneMat Ω (ν x))ᴴ := by
  have h1 : (Ω (ν x))ᴴ * Ω (ν x) = 1 := hΩ.star_mul_self _ (norm_equator_le_one hc x)
  have h2 : (Ω (seamPoint t ν x))ᴴ * Ω (seamPoint t ν x) = 1 :=
    hΩ.star_mul_self _ (norm_seamPoint_le_one t ν x)
  have hinner : (Ω (seamPoint t ν x))ᴴ * (Ω (ν x))ᴴ *
      (Ω (ν x) * Ω (seamPoint t ν x) * (Ω (chartDir ν x))ᴴ) = (Ω (chartDir ν x))ᴴ := by
    calc (Ω (seamPoint t ν x))ᴴ * (Ω (ν x))ᴴ *
          (Ω (ν x) * Ω (seamPoint t ν x) * (Ω (chartDir ν x))ᴴ)
        = (Ω (seamPoint t ν x))ᴴ * ((Ω (ν x))ᴴ * Ω (ν x)) *
            (Ω (seamPoint t ν x) * (Ω (chartDir ν x))ᴴ) := by
          simp only [Matrix.mul_assoc]
      _ = (Ω (seamPoint t ν x))ᴴ * (Ω (seamPoint t ν x) * (Ω (chartDir ν x))ᴴ) := by
          rw [h1, Matrix.mul_one]
      _ = ((Ω (seamPoint t ν x))ᴴ * Ω (seamPoint t ν x)) * (Ω (chartDir ν x))ᴴ := by
          rw [Matrix.mul_assoc]
      _ = (Ω (chartDir ν x))ᴴ := by rw [h2, Matrix.one_mul]
  have hOff : (twistedCone ν Ω x)ᴴ = ((‖ν x‖ : ℝ) : ℂ) • (Ω (ν x))ᴴ := by
    rw [twistedCone_def, Matrix.conjTranspose_smul, star_ofReal_complex]
  have hFf : (coneMat Ω (ν x))ᴴ = ((‖ν x‖ : ℝ) : ℂ) • (Ω (chartDir ν x))ᴴ := by
    rw [coneMat_apply_equator, Matrix.conjTranspose_smul, star_ofReal_complex]
  rw [hOff, hFf, seamGauge_def, seamCorrection_def, Matrix.mul_smul, Matrix.smul_mul, hinner]

/-! ### Continuity of the four blocks -/

theorem continuousAt_chartDir (hc : IsSuspensionChart t ν) {x₀ : X} (hx : ν x₀ ≠ 0) :
    ContinuousAt (chartDir ν) x₀ := by
  have hopen := isOpen_equator_ne hc
  have hinv : ContinuousOn (fun x => (‖ν x‖)⁻¹) {x : X | ν x ≠ 0} :=
    ContinuousOn.inv₀ hc.continuous_equator.norm.continuousOn
      fun x hx => norm_ne_zero_iff.mpr hx
  have hmain : ContinuousOn (chartDir ν) {x : X | ν x ≠ 0} := by
    have h : ContinuousOn (fun x => (‖ν x‖)⁻¹ • ν x) {x : X | ν x ≠ 0} :=
      hinv.smul hc.continuous_equator.continuousOn
    exact h
  exact hmain.continuousAt (hopen.mem_nhds hx)

theorem continuousAt_seamPoint_of_ne (hc : IsSuspensionChart t ν) {x₀ : X} (hx : ν x₀ ≠ 0) :
    ContinuousAt (seamPoint t ν) x₀ := by
  have hopen := isOpen_equator_ne hc
  have hinv : ContinuousOn (fun x => (‖ν x‖)⁻¹) {x : X | ν x ≠ 0} :=
    ContinuousOn.inv₀ hc.continuous_equator.norm.continuousOn
      fun x hx => norm_ne_zero_iff.mpr hx
  have hmain : ContinuousOn (seamPoint t ν) {x : X | ν x ≠ 0} := by
    have h : ContinuousOn (fun x => (seamParam (t x) * (‖ν x‖)⁻¹) • ν x) {x : X | ν x ≠ 0} :=
      (((continuous_seamParam.comp hc.continuous_height).continuousOn).mul hinv).smul
        hc.continuous_equator.continuousOn
    exact h
  exact hmain.continuousAt (hopen.mem_nhds hx)

theorem continuousAt_seamPoint (hc : IsSuspensionChart t ν) {x₀ : X} (hx : t x₀ ≠ -1) :
    ContinuousAt (seamPoint t ν) x₀ := by
  rcases eq_or_ne (ν x₀) 0 with h | h
  · have ht1 : t x₀ = 1 := by
      rcases height_eq_of_equator_zero hc h with h1 | h1
      · exact h1
      · exact absurd h1 hx
    refine continuousAt_of_norm_le (r := fun y => seamParam (t y))
      (fun y => norm_seamPoint_le t ν y) ?_ ?_
    · have hten : Filter.Tendsto (fun y => seamParam (t y)) (nhds x₀) (nhds (seamParam (t x₀))) :=
        (continuous_seamParam.comp hc.continuous_height).continuousAt
      rwa [ht1, seamParam_one] at hten
    · rw [seamPoint_def, h, smul_zero]
  · exact continuousAt_seamPoint_of_ne hc h

theorem continuousAt_seamGauge (hc : IsSuspensionChart t ν) (hΩ : IsDiscUnitary Ω) {x₀ : X}
    (hx : t x₀ ≠ -1) : ContinuousAt (seamGauge t ν Ω) x₀ :=
  hΩ.continuous.continuousAt.comp (continuousAt_seamPoint hc hx)

/-- On a collar around the south pole the seam gauge equals the clutching
function itself, so the seam correction collapses to `Ω ∘ ν`.  This plateau is
what makes the correction continuous at the south pole, where the gauge itself
is not. -/
theorem seamCorrection_eq_of_lt (hΩ : IsDiscUnitary Ω) {x : X} (hx : t x < -(1 / 2)) :
    seamCorrection t ν Ω x = Ω (ν x) := by
  have hsp : seamParam (t x) = 1 := seamParam_of_le (le_of_lt hx)
  have hpt : seamPoint t ν x = chartDir ν x := by
    rw [seamPoint_def, hsp, one_mul, chartDir_def]
  rw [seamCorrection_def, hpt, Matrix.mul_assoc,
    hΩ.mul_star_self _ (norm_chartDir_le_one ν x), Matrix.mul_one]

theorem continuousAt_seamCorrection (hc : IsSuspensionChart t ν) (hΩ : IsDiscUnitary Ω) {x₀ : X}
    (hx : t x₀ ≠ 1) : ContinuousAt (seamCorrection t ν Ω) x₀ := by
  rcases eq_or_ne (ν x₀) 0 with h | h
  · have ht1 : t x₀ = -1 := by
      rcases height_eq_of_equator_zero hc h with h1 | h1
      · exact absurd h1 hx
      · exact h1
    have hW : IsOpen {y : X | t y < -(1 / 2 : ℝ)} :=
      isOpen_lt hc.continuous_height continuous_const
    have hmem : x₀ ∈ {y : X | t y < -(1 / 2 : ℝ)} := by
      show t x₀ < -(1 / 2 : ℝ)
      rw [ht1]
      norm_num
    have heq : Set.EqOn (fun y => Ω (ν y)) (seamCorrection t ν Ω)
        {y : X | t y < -(1 / 2 : ℝ)} := fun y hy => (seamCorrection_eq_of_lt hΩ hy).symm
    exact ContinuousAt.congr (hΩ.continuous.comp hc.continuous_equator).continuousAt
      (Filter.eventuallyEq_of_mem (hW.mem_nhds hmem) heq)
  · have hA : ContinuousAt (fun y => Ω (ν y)) x₀ :=
      hΩ.continuous.continuousAt.comp hc.continuous_equator.continuousAt
    have hB : ContinuousAt (fun y => Ω (seamPoint t ν y)) x₀ :=
      hΩ.continuous.continuousAt.comp (continuousAt_seamPoint_of_ne hc h)
    have hC : ContinuousAt (fun y => (Ω (chartDir ν y))ᴴ) x₀ := by
      have hD : ContinuousAt (fun y => Ω (chartDir ν y)) x₀ :=
        hΩ.continuous.continuousAt.comp (continuousAt_chartDir hc h)
      exact hD.star
    exact (hA.mul hB).mul hC

/-! ### The main theorem -/

/-- **Null-homotopy kills the twist.**

If the clutching function extends to a continuous unitary-valued map `Ω` on
the closed unit ball of `E` -- equivalently, if it is null-homotopic -- then
the clutched projection is Murray--von Neumann equivalent to the untwisted
one, and the implementing partial isometry is produced explicitly and
continuously.

This is the reduction the LIX argument needs: contrapositively, if the
clutched projection is *not* equivalent to the untwisted one, then the
clutching function is not null-homotopic. -/
theorem exists_partialIsometry_of_isDiscUnitary (hc : IsSuspensionChart t ν)
    (hΩ : IsDiscUnitary Ω) :
    ∃ V : X → Matrix (n ⊕ n) (n ⊕ n) ℂ, Continuous V ∧
      (∀ x, (V x)ᴴ * V x = clutchMat (t x) (coneMat Ω (ν x))) ∧
      (∀ x, V x * (V x)ᴴ =
        clutchMat (t x) (((‖ν x‖ : ℝ) : ℂ) • (1 : Matrix n n ℂ))) := by
  classical
  -- unitarity of every `Ω`-value in sight
  have hΩν : ∀ x, (Ω (ν x))ᴴ * Ω (ν x) = 1 :=
    fun x => hΩ.star_mul_self _ (norm_equator_le_one hc x)
  have hΩν' : ∀ x, Ω (ν x) * (Ω (ν x))ᴴ = 1 :=
    fun x => hΩ.mul_star_self _ (norm_equator_le_one hc x)
  have hΩd : ∀ x, (Ω (chartDir ν x))ᴴ * Ω (chartDir ν x) = 1 :=
    fun x => hΩ.star_mul_self _ (norm_chartDir_le_one ν x)
  have hΩd' : ∀ x, Ω (chartDir ν x) * (Ω (chartDir ν x))ᴴ = 1 :=
    fun x => hΩ.mul_star_self _ (norm_chartDir_le_one ν x)
  have hΩμ : ∀ x, (seamGauge t ν Ω x)ᴴ * seamGauge t ν Ω x = 1 :=
    fun x => hΩ.star_mul_self _ (norm_seamPoint_le_one t ν x)
  have hΩμ' : ∀ x, seamGauge t ν Ω x * (seamGauge t ν Ω x)ᴴ = 1 :=
    fun x => hΩ.mul_star_self _ (norm_seamPoint_le_one t ν x)
  have hmu : ∀ x, (seamCorrection t ν Ω x)ᴴ * seamCorrection t ν Ω x = 1 ∧
      seamCorrection t ν Ω x * (seamCorrection t ν Ω x)ᴴ = 1 := by
    intro x
    have h1 := unitary_mul_unitary (hΩν x) (hΩν' x) (hΩμ x) (hΩμ' x)
    have h2 : ((Ω (chartDir ν x))ᴴ)ᴴ * (Ω (chartDir ν x))ᴴ = 1 := by
      rw [Matrix.conjTranspose_conjTranspose]; exact hΩd' x
    have h3 : (Ω (chartDir ν x))ᴴ * ((Ω (chartDir ν x))ᴴ)ᴴ = 1 := by
      rw [Matrix.conjTranspose_conjTranspose]; exact hΩd x
    exact unitary_mul_unitary h1.1 h1.2 h2 h3
  -- the clutching data
  have hfd : ∀ x, IsClutchDatum (t x) (coneMat Ω (ν x)) :=
    fun x => isClutchDatum_coneMat hΩ (hc.sphere x)
  have hgd : ∀ x, IsClutchDatum (t x) (twistedCone ν Ω x) :=
    fun x => isClutchDatum_twistedCone hc hΩ x
  -- the seam isometry and the change of hemisphere trivialisation
  have hV₀star : ∀ x, (seamMat (t x) (coneMat Ω (ν x)) (twistedCone ν Ω x) (seamGauge t ν Ω x)
      (seamCorrection t ν Ω x))ᴴ *
      seamMat (t x) (coneMat Ω (ν x)) (twistedCone ν Ω x) (seamGauge t ν Ω x)
      (seamCorrection t ν Ω x) = clutchMat (t x) (coneMat Ω (ν x)) := fun x =>
    seamMat_conjTranspose_mul_self (hfd x) (hgd x) (hΩμ x) (hmu x).1
      (seam_identity hc hΩ x)
  have hV₀star' : ∀ x, seamMat (t x) (coneMat Ω (ν x)) (twistedCone ν Ω x) (seamGauge t ν Ω x)
      (seamCorrection t ν Ω x) *
      (seamMat (t x) (coneMat Ω (ν x)) (twistedCone ν Ω x) (seamGauge t ν Ω x)
      (seamCorrection t ν Ω x))ᴴ = clutchMat (t x) (twistedCone ν Ω x) := fun x =>
    seamMat_mul_conjTranspose (hfd x) (hgd x) (hΩμ' x) (hmu x).2 (seam_identity hc hΩ x)
  refine ⟨fun x => (clutchConj (Ω (ν x)))ᴴ *
    seamMat (t x) (coneMat Ω (ν x)) (twistedCone ν Ω x) (seamGauge t ν Ω x)
      (seamCorrection t ν Ω x), ?_, ?_, ?_⟩
  · -- continuity
    have hb1 : ∀ x i j, ‖seamGauge t ν Ω x i j‖ ≤ 1 := fun x => norm_entry_le_one (hΩμ x)
    have hb2 : ∀ x i j, ‖(seamGauge t ν Ω x * (Ω (chartDir ν x))ᴴ) i j‖ ≤ 1 := by
      intro x
      have h2 : ((Ω (chartDir ν x))ᴴ)ᴴ * (Ω (chartDir ν x))ᴴ = 1 := by
        rw [Matrix.conjTranspose_conjTranspose]; exact hΩd' x
      have h3 : (Ω (chartDir ν x))ᴴ * ((Ω (chartDir ν x))ᴴ)ᴴ = 1 := by
        rw [Matrix.conjTranspose_conjTranspose]; exact hΩd x
      exact norm_entry_le_one (unitary_mul_unitary (hΩμ x) (hΩμ' x) h2 h3).1
    have hb3 : ∀ x i j, ‖(Ω (ν x) * seamGauge t ν Ω x) i j‖ ≤ 1 := fun x =>
      norm_entry_le_one (unitary_mul_unitary (hΩν x) (hΩν' x) (hΩμ x) (hΩμ' x)).1
    have hb4 : ∀ x i j, ‖seamCorrection t ν Ω x i j‖ ≤ 1 := fun x =>
      norm_entry_le_one (hmu x).1
    -- block 1
    have hblock1 : Continuous fun x =>
        ((((1 + t x) / 2 : ℝ)) : ℂ) • seamGauge t ν Ω x := by
      refine continuous_damped (U := {x : X | t x ≠ -1})
        (isOpen_compl_singleton.preimage hc.continuous_height)
        ((continuous_const.add hc.continuous_height).div_const 2) ?_ hb1 ?_
      · exact continuousOn_of_forall_continuousAt fun x hx => continuousAt_seamGauge hc hΩ hx
      · intro x hx
        have : t x = -1 := by simpa using hx
        rw [this]
        norm_num
    -- block 4
    have hblock4 : Continuous fun x =>
        ((((1 - t x) / 2 : ℝ)) : ℂ) • seamCorrection t ν Ω x := by
      refine continuous_damped (U := {x : X | t x ≠ 1})
        (isOpen_compl_singleton.preimage hc.continuous_height)
        ((continuous_const.sub hc.continuous_height).div_const 2) ?_ hb4 ?_
      · exact continuousOn_of_forall_continuousAt fun x hx =>
          continuousAt_seamCorrection hc hΩ hx
      · intro x hx
        have : t x = 1 := by simpa using hx
        rw [this]
        norm_num
    -- block 2
    have hblock2 : Continuous fun x =>
        ((‖ν x‖ / 2 : ℝ) : ℂ) • (seamGauge t ν Ω x * (Ω (chartDir ν x))ᴴ) := by
      refine continuous_damped (U := {x : X | ν x ≠ 0}) (isOpen_equator_ne hc)
        (hc.continuous_equator.norm.div_const 2) ?_ hb2 ?_
      · refine continuousOn_of_forall_continuousAt fun x hx => ?_
        have hB : ContinuousAt (fun y => Ω (seamPoint t ν y)) x :=
          hΩ.continuous.continuousAt.comp (continuousAt_seamPoint_of_ne hc hx)
        have hC : ContinuousAt (fun y => (Ω (chartDir ν y))ᴴ) x := by
          have hD : ContinuousAt (fun y => Ω (chartDir ν y)) x :=
            hΩ.continuous.continuousAt.comp (continuousAt_chartDir hc hx)
          exact hD.star
        exact hB.mul hC
      · intro x hx
        have h0 : ν x = 0 := by simpa using hx
        rw [h0]
        norm_num
    -- block 3
    have hblock3 : Continuous fun x =>
        ((‖ν x‖ / 2 : ℝ) : ℂ) • (Ω (ν x) * seamGauge t ν Ω x) := by
      refine continuous_damped (U := {x : X | ν x ≠ 0}) (isOpen_equator_ne hc)
        (hc.continuous_equator.norm.div_const 2) ?_ hb3 ?_
      · refine continuousOn_of_forall_continuousAt fun x hx => ?_
        have hA : ContinuousAt (fun y => Ω (ν y)) x :=
          hΩ.continuous.continuousAt.comp hc.continuous_equator.continuousAt
        have hB : ContinuousAt (fun y => Ω (seamPoint t ν y)) x :=
          hΩ.continuous.continuousAt.comp (continuousAt_seamPoint_of_ne hc hx)
        exact hA.mul hB
      · intro x hx
        have h0 : ν x = 0 := by simpa using hx
        rw [h0]
        norm_num
    have hV₀cont : Continuous (fun x => seamMat (t x) (coneMat Ω (ν x)) (twistedCone ν Ω x) (seamGauge t ν Ω x)
      (seamCorrection t ν Ω x)) := by
      have hrw : (fun x => seamMat (t x) (coneMat Ω (ν x)) (twistedCone ν Ω x) (seamGauge t ν Ω x)
      (seamCorrection t ν Ω x)) = fun x => Matrix.fromBlocks
          (((((1 + t x) / 2 : ℝ)) : ℂ) • seamGauge t ν Ω x)
          (((‖ν x‖ / 2 : ℝ) : ℂ) • (seamGauge t ν Ω x * (Ω (chartDir ν x))ᴴ))
          (((‖ν x‖ / 2 : ℝ) : ℂ) • (Ω (ν x) * seamGauge t ν Ω x))
          (((((1 - t x) / 2 : ℝ)) : ℂ) • seamCorrection t ν Ω x) := by
        funext x
        rw [seamMat, Matrix.fromBlocks_inj]
        refine ⟨rfl, ?_, ?_, rfl⟩
        · rw [coneMat_apply_equator, Matrix.conjTranspose_smul, star_ofReal_complex,
            Matrix.mul_smul, smul_smul,
            show ((1 / 2 : ℂ) * ((‖ν x‖ : ℝ) : ℂ)) = ((‖ν x‖ / 2 : ℝ) : ℂ) by
              push_cast; ring]
        · rw [twistedCone_def, Matrix.smul_mul, smul_smul,
            show ((1 / 2 : ℂ) * ((‖ν x‖ : ℝ) : ℂ)) = ((‖ν x‖ / 2 : ℝ) : ℂ) by
              push_cast; ring]
      rw [hrw]
      exact continuous_fromBlocks hblock1 hblock2 hblock3 hblock4
    exact (continuous_clutchConj (hΩ.continuous.comp hc.continuous_equator)).star.mul hV₀cont
  · intro x
    have hU := clutchConj_mul_conjTranspose_self (hΩν' x)
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc,
      ← Matrix.mul_assoc (clutchConj (Ω (ν x))), hU, Matrix.one_mul]
    exact hV₀star x
  · intro x
    have hU := clutchConj_conjTranspose_mul_self (hΩν x)
    have hconj : clutchConj (Ω (ν x)) *
        clutchMat (t x) (((‖ν x‖ : ℝ) : ℂ) • (1 : Matrix n n ℂ)) *
        (clutchConj (Ω (ν x)))ᴴ = clutchMat (t x) (twistedCone ν Ω x) := by
      rw [clutchConj_mul_clutchMat_mul_conjTranspose (t x) (hΩν' x), twistedCone_def,
        Matrix.mul_smul, Matrix.mul_one]
    have key : ∀ P : Matrix (n ⊕ n) (n ⊕ n) ℂ, (clutchConj (Ω (ν x)))ᴴ *
        (clutchConj (Ω (ν x)) * P * (clutchConj (Ω (ν x)))ᴴ) * clutchConj (Ω (ν x)) = P := by
      intro P
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hU, Matrix.one_mul, Matrix.mul_assoc, hU,
        Matrix.mul_one]
    calc (clutchConj (Ω (ν x)))ᴴ * seamMat (t x) (coneMat Ω (ν x)) (twistedCone ν Ω x) (seamGauge t ν Ω x)
      (seamCorrection t ν Ω x) *
          ((clutchConj (Ω (ν x)))ᴴ * seamMat (t x) (coneMat Ω (ν x)) (twistedCone ν Ω x) (seamGauge t ν Ω x)
      (seamCorrection t ν Ω x))ᴴ
        = (clutchConj (Ω (ν x)))ᴴ * (seamMat (t x) (coneMat Ω (ν x)) (twistedCone ν Ω x) (seamGauge t ν Ω x)
      (seamCorrection t ν Ω x) *
            (seamMat (t x) (coneMat Ω (ν x)) (twistedCone ν Ω x) (seamGauge t ν Ω x)
      (seamCorrection t ν Ω x))ᴴ) * clutchConj (Ω (ν x)) := by
          rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
          simp only [Matrix.mul_assoc]
      _ = (clutchConj (Ω (ν x)))ᴴ * clutchMat (t x) (twistedCone ν Ω x) *
            clutchConj (Ω (ν x)) := by rw [hV₀star' x]
      _ = (clutchConj (Ω (ν x)))ᴴ * (clutchConj (Ω (ν x)) *
            clutchMat (t x) (((‖ν x‖ : ℝ) : ℂ) • (1 : Matrix n n ℂ)) *
            (clutchConj (Ω (ν x)))ᴴ) * clutchConj (Ω (ν x)) := by rw [hconj]
      _ = clutchMat (t x) (((‖ν x‖ : ℝ) : ℂ) • (1 : Matrix n n ℂ)) := key _

end NullHomotopy

/-! ## The interface owed by the obstruction lane -/

section Obstruction

variable {X : Type*} [TopologicalSpace X] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace ℝ E] {n : Type*} [Fintype n] [DecidableEq n]

/-- **The obstruction interface.**

`ClutchingObstruction t ν Ω` asserts that the projection clutched by `Ω` over
the suspension chart `(t, ν)` is *not* Murray--von Neumann equivalent to the
untwisted projection of the same rank: there is no continuous field of
matrices `V` with `VᴴV` the clutched projection and `VVᴴ` the untwisted one.

By `exists_partialIsometry_of_isDiscUnitary` this is exactly the statement
that the clutching function does not extend to a continuous unitary-valued map
on the closed unit ball, i.e. that it is not null-homotopic.  Nothing in this
file proves any instance of it: for the LIX counterexample the instance needed
is the manuscript's Lemma 2, `F ⊕ H ≇ 1² ⊕ H` over `S⁵ × Y`, whose proof is
the mapping-torus parity calculation.  That is the obstruction lane's
deliverable, and it is the *only* input this layer needs in order to conclude
that the manuscript's comparison unitary is not null-homotopic. -/
def ClutchingObstruction (t : X → ℝ) (ν : X → E) (Ω : E → Matrix n n ℂ) : Prop :=
  ¬ ∃ V : X → Matrix (n ⊕ n) (n ⊕ n) ℂ, Continuous V ∧
    (∀ x, (V x)ᴴ * V x = clutchMat (t x) (coneMat Ω (ν x))) ∧
    (∀ x, V x * (V x)ᴴ =
      clutchMat (t x) (((‖ν x‖ : ℝ) : ℂ) • (1 : Matrix n n ℂ)))

/-- **The reduction is airtight.**  A single obstruction input finishes the
argument: if the clutched projection is not equivalent to the untwisted one,
then the clutching function admits no disc extension -- it is not
null-homotopic. -/
theorem not_isDiscUnitary_of_clutchingObstruction {t : X → ℝ} {ν : X → E}
    {Ω : E → Matrix n n ℂ} (hc : IsSuspensionChart t ν)
    (hobs : ClutchingObstruction t ν Ω) : ¬ IsDiscUnitary Ω :=
  fun hΩ => hobs (exists_partialIsometry_of_isDiscUnitary hc hΩ)

/-- A partial isometry absorbs its initial projection. -/
theorem mul_source_of_partialIsometry {ι : Type*} [Fintype ι] [DecidableEq ι]
    {W q : Matrix ι ι ℂ} (hq : Wᴴ * W = q) (hidem : q * q = q) : W * q = W := by
  have hqs : qᴴ = q := by
    rw [← hq, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have hzero : (W * q - W)ᴴ * (W * q - W) = 0 := by
    have e : (W * q - W)ᴴ * (W * q - W)
        = q * (Wᴴ * W) * q - q * (Wᴴ * W) - Wᴴ * W * q + Wᴴ * W := by
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hqs]
      noncomm_ring
    rw [e, hq]
    simp only [hidem]
    noncomm_ring
  have h := Matrix.conjTranspose_mul_self_eq_zero.mp hzero
  exact sub_eq_zero.mp h

/-- **The obstruction transports along Murray--von Neumann equivalence.**

If the clutched projection is equivalent to some other projection field `P`,
and `P` is not equivalent to the untwisted projection, then the clutching
function carries the obstruction.  This is how the obstruction lane may
deliver the manuscript's Lemma 2 in whatever concrete model it prefers -- for
instance for `F ⊕ H` over `S⁵ × Y` with `F x = 1 - x xᴴ` -- without having to
speak the clutching vocabulary at all. -/
theorem clutchingObstruction_of_equiv {t : X → ℝ} {ν : X → E}
    {Ω : E → Matrix n n ℂ}
    {P : X → Matrix (n ⊕ n) (n ⊕ n) ℂ}
    (hc : IsSuspensionChart t ν) (hΩ : IsDiscUnitary Ω)
    (W : X → Matrix (n ⊕ n) (n ⊕ n) ℂ) (hW : Continuous W)
    (hW1 : ∀ x, (W x)ᴴ * W x = clutchMat (t x) (coneMat Ω (ν x)))
    (hW2 : ∀ x, W x * (W x)ᴴ = P x)
    (hP : ¬ ∃ V : X → Matrix (n ⊕ n) (n ⊕ n) ℂ, Continuous V ∧
      (∀ x, (V x)ᴴ * V x = P x) ∧
      (∀ x, V x * (V x)ᴴ =
        clutchMat (t x) (((‖ν x‖ : ℝ) : ℂ) • (1 : Matrix n n ℂ)))) :
    ClutchingObstruction t ν Ω := by
  rintro ⟨V, hVc, hV1, hV2⟩
  have hidem : ∀ x, clutchMat (t x) (coneMat Ω (ν x)) * clutchMat (t x) (coneMat Ω (ν x))
      = clutchMat (t x) (coneMat Ω (ν x)) :=
    fun x => clutchMat_mul_self (isClutchDatum_coneMat hΩ (hc.sphere x))
  refine hP ⟨fun x => V x * (W x)ᴴ, hVc.mul hW.star, fun x => ?_, fun x => ?_⟩
  · have hWabs : W x * clutchMat (t x) (coneMat Ω (ν x)) = W x :=
      mul_source_of_partialIsometry (hW1 x) (hidem x)
    calc (V x * (W x)ᴴ)ᴴ * (V x * (W x)ᴴ)
        = W x * ((V x)ᴴ * V x) * (W x)ᴴ := by
          rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
          simp only [Matrix.mul_assoc]
      _ = W x * clutchMat (t x) (coneMat Ω (ν x)) * (W x)ᴴ := by rw [hV1 x]
      _ = W x * (W x)ᴴ := by rw [hWabs]
      _ = P x := hW2 x
  · have hVabs : V x * clutchMat (t x) (coneMat Ω (ν x)) = V x :=
      mul_source_of_partialIsometry (hV1 x) (hidem x)
    calc (V x * (W x)ᴴ) * (V x * (W x)ᴴ)ᴴ
        = V x * ((W x)ᴴ * W x) * (V x)ᴴ := by
          rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
          simp only [Matrix.mul_assoc]
      _ = V x * clutchMat (t x) (coneMat Ω (ν x)) * (V x)ᴴ := by rw [hW1 x]
      _ = V x * (V x)ᴴ := by rw [hVabs]
      _ = _ := hV2 x

end Obstruction

/-! ## Instantiating the suspension chart -/

section Charts

variable {X : Type*} [TopologicalSpace X] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace ℝ E]

/-- A suspension chart pulls back along any continuous map.  This is the
interoperability hook: a lane owning a concrete model of `S^{n+1}` supplies a
continuous map into the split sphere below (or its two coordinates directly)
and inherits the entire clutching layer. -/
theorem IsSuspensionChart.comp {Y : Type*} [TopologicalSpace Y] {t : X → ℝ} {ν : X → E}
    (h : IsSuspensionChart t ν) {φ : Y → X} (hφ : Continuous φ) :
    IsSuspensionChart (fun y => t (φ y)) (fun y => ν (φ y)) where
  continuous_height := h.continuous_height.comp hφ
  continuous_equator := h.continuous_equator.comp hφ
  sphere := fun y => h.sphere (φ y)

/-- The **split sphere** of `E`: the unit sphere of `E × ℝ` for the Euclidean
combination of the two norms.  It is the tautological carrier of a suspension
chart. -/
def SplitSphere (E : Type*) [NormedAddCommGroup E] : Type _ :=
  {p : E × ℝ // ‖p.1‖ ^ 2 + p.2 ^ 2 = 1}

instance : TopologicalSpace (SplitSphere E) :=
  inferInstanceAs (TopologicalSpace {p : E × ℝ // ‖p.1‖ ^ 2 + p.2 ^ 2 = 1})

/-- The tautological suspension chart. -/
theorem isSuspensionChart_splitSphere :
    IsSuspensionChart (fun p : SplitSphere E => p.val.2) (fun p : SplitSphere E => p.val.1) where
  continuous_height := continuous_snd.comp continuous_subtype_val
  continuous_equator := continuous_fst.comp continuous_subtype_val
  sphere := fun p => p.property

/-- The clutching layer sees a concrete sphere only through a continuous map
into a split sphere.  For `S^{n+1} ⊆ ℝ^{n+2}` with the last coordinate as the
height and `E = EuclideanSpace ℝ (Fin (n+1))` as the equatorial space, that
map is `x ↦ ⟨(x ∘ castSucc, x (last _)), _⟩`, and its defining identity is
`Fin.sum_univ_castSucc` applied to `EuclideanSpace.real_norm_sq_eq`.  Supplying
it is the concrete-model lane's job; nothing in this file needs to know which
model is chosen. -/
theorem isSuspensionChart_of_map {Y : Type*} [TopologicalSpace Y]
    (φ : Y → SplitSphere E) (hφ : Continuous φ) :
    IsSuspensionChart (fun y => (φ y).val.2) (fun y => (φ y).val.1) :=
  isSuspensionChart_splitSphere.comp hφ

end Charts

end

end LIX
end GroupApproximation
