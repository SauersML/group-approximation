import GroupApproximation.Analysis.ReducedGroupCStarMFObstruction
import GroupApproximation.Analysis.ReducedGroupCStarTraceFaithful
import GroupApproximation.Sofic.LiteralNonMFEndpoint

/-!
# Finite dimensionality of the coordinates cannot be traded for faithful traces

The manuscript's limitations section makes one negative claim beyond the
positive theory: finite dimensionality of the coordinate algebras in the
Kazhdan transport theorem is essential in a sharper sense than the choice of
norm, because *it cannot be traded for stable finiteness of the coordinate
algebras together with faithful traces*.  The refutation printed there is the
constant coordinate sequence `A n = C⋆_r(E)`: the left regular representation
embeds `E` injectively, `c` centralizes the Kazhdan base there, conjugation by
`t` produces `t c t⁻¹`, and the commutator of that with the base is precisely
the nontrivial defect that Theorem A detects.  A transport theorem stated for
faithfully traced coordinates would collapse that commutator.

This file makes that argument machine-checked.

## What is stated

`FaithfullyTracedCoordinateTransport` is the literal analogue of
`KazhdanAsymptoticCommutant.manuscriptKazhdanTransport`, obtained from it by
three substitutions and nothing else:

* the matrix coordinates `M_{d n}(ℂ)` become an arbitrary sequence `A n` of
  unital C⋆-algebras;
* the normalized Hilbert--Schmidt norm becomes the trace 2-norm
  `‖y‖_τ = √(τ(y⋆y))` of a faithful tracial state `τ n` on `A n`;
* every other hypothesis --- property `(T)` for the source, the compressor
  normalizing the image, asymptotic multiplicativity of the unitaries in
  operator norm, a uniform norm bound on the transported element --- is
  copied verbatim.

Two remarks on faithfulness of the transcription.

*Finiteness is printed, not smuggled.*  The manuscript's sentence pairs
faithful traces with stable finiteness, so the candidate property carries the
finiteness hypothesis explicitly, in the C⋆-form the repository already uses:
every isometry in every coordinate is unitary.  That hypothesis is redundant
--- `FaithfulTracialState.mul_star_eq_one_of_star_mul_eq_one` derives it from
the trace --- but printing it keeps the refuted statement visibly the one the
manuscript names, and a redundant hypothesis can only make the no-go harder to
prove, never easier.

*Conjugation is written with `star`.*  The matrix statement conjugates by
`U n s * x n * (U n s)⁻¹`; here the same conjugation is written
`U n s * x n * star (U n s)`, which is the same element because `u⁻¹ = star u`
for a unitary.  Writing it with `star` keeps the statement inside the ring and
avoids a coercion from the unitary group.

## What is proved

`not_faithfullyTracedCoordinateTransport_of_core` refutes the property from
*any* `KazhdanCompressionCore` with one nontrivial pointwise compression
defect, and `manuscriptFaithfullyTracedCoordinateNoGo` instantiates it at the
manuscript's own datum: `LiteralNonMFEndpoint.inclusionData`, whose defect is
nontrivial because its square is the literal mark.

The refutation is exactly the manuscript's.  In the constant coordinates
`A n = C⋆_r(E)` the almost-multiplicativity hypothesis holds with defect zero,
the hypothesis on `x = λ(c)` holds with commutator zero because `c` centralizes
the Kazhdan image, and the conclusion at a single coordinate forces
`λ(t c t⁻¹ · ι γ) = λ(ι γ · t c t⁻¹)` exactly, since a faithful trace has no
kernel and the sequence is constant.  Injectivity of the left regular
representation then puts the collapse back in the group, where the defect is
nontrivial.

Note what the refutation does *not* need: no exotic property-`(T)` group, no
failure of the operator-norm theorem, and no analysis beyond the faithfulness
of one trace.  The finite-dimensional theorem and this no-go share every
hypothesis except the coordinates.
-/

namespace GroupApproximation
namespace FaithfullyTracedCoordinates

open ReducedGroupCStarTrace
open scoped ComplexOrder commutatorElement

noncomputable section

universe w

/-! ## The trace 2-norm of a faithful tracial state -/

section TraceTwoNorm

variable {B : Type*} [Ring B] [StarRing B] [Algebra ℂ B]

/-- The 2-norm attached to a faithful tracial state, `‖y‖_τ = √(τ(y⋆y))`.
This is the coordinate-algebra analogue of the normalized Hilbert--Schmidt
norm of a matrix coordinate: it is the norm in which the transport theorem
measures commutators. -/
def traceTwoNorm (τ : FaithfulTracialState B) (y : B) : ℝ :=
  Real.sqrt (τ (star y * y)).re

@[simp] theorem traceTwoNorm_def (τ : FaithfulTracialState B) (y : B) :
    traceTwoNorm τ y = Real.sqrt (τ (star y * y)).re := rfl

@[simp] theorem traceTwoNorm_zero (τ : FaithfulTracialState B) :
    traceTwoNorm τ (0 : B) = 0 := by
  rw [traceTwoNorm_def, mul_zero, FaithfulTracialState.map_zero, Complex.zero_re,
    Real.sqrt_zero]

/-- Faithfulness, in the form the no-go consumes: an element whose trace
2-norm is below every positive tolerance is zero.  This is the step that a
finite-dimensional coordinate never needed and that a general faithfully
traced coordinate supplies for free. -/
theorem eq_zero_of_traceTwoNorm_le (τ : FaithfulTracialState B) {y : B}
    (h : ∀ ε : ℝ, 0 < ε → traceTwoNorm τ y ≤ ε) : y = 0 := by
  by_contra hy
  have hne : τ (star y * y) ≠ 0 := fun h0 ↦
    hy ((τ.map_star_mul_self_eq_zero_iff y).mp h0)
  have hnn : (0 : ℂ) ≤ τ (star y * y) := τ.map_star_mul_self_nonneg y
  rw [Complex.le_def, Complex.zero_re, Complex.zero_im] at hnn
  obtain ⟨hre, him⟩ := hnn
  have hpos : 0 < (τ (star y * y)).re := by
    rcases hre.lt_or_eq with hlt | heq
    · exact hlt
    · exact absurd (Complex.ext heq.symm him.symm) hne
  have hsqrt : 0 < Real.sqrt ((τ (star y * y)).re) := Real.sqrt_pos.mpr hpos
  have hhalf := h (Real.sqrt ((τ (star y * y)).re) / 2) (by linarith)
  rw [traceTwoNorm_def] at hhalf
  linarith

end TraceTwoNorm

/-! ## The candidate faithfully traced coordinate transport theorem -/

/-- Convergence of a commutator to zero in the trace 2-norm of the coordinate
traces.  This is the exact analogue of
`KazhdanAsymptoticCommutant.NaturalHSCommutatorVanishing`, with the normalized
Hilbert--Schmidt norm of a matrix coordinate replaced by the trace 2-norm of a
faithfully traced coordinate. -/
def TracialCommutatorVanishing {H : Type} [Group H]
    (A : ℕ → Type) [∀ n, CStarAlgebra (A n)]
    (τ : ∀ n, FaithfulTracialState (A n))
    (U : ∀ n, H → unitary (A n))
    (x : ∀ n, A n) (g : H) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
    traceTwoNorm (τ n) (x n * (U n g : A n) - (U n g : A n) * x n) ≤ ε

/-- **The candidate generalization of Kazhdan transport to faithfully traced
coordinates.**  Every hypothesis of `manuscriptKazhdanTransport` is copied:
property `(T)` for the source, a compressor normalizing its image, asymptotic
multiplicativity of the coordinate unitaries in operator norm, a uniform norm
bound on the transported element, and vanishing of its commutators with the
Kazhdan image.  The only changes are the coordinates --- an arbitrary sequence
of unital C⋆-algebras, each finite and each carrying a faithful tracial
state --- and the norm in which commutators are measured.

The next theorem shows this property is false. -/
def FaithfullyTracedCoordinateTransport : Prop :=
  ∀ (Γ H : Type) [Group Γ] [Group H],
    HasKazhdanPropertyTComplex.{0, w} Γ →
    ∀ (iota : Γ →* H) (s : H),
      (∀ γ : Γ, ∃ δ : Γ, s * iota γ * s⁻¹ = iota δ) →
      ∀ (A : ℕ → Type) [∀ n, CStarAlgebra (A n)]
        (τ : ∀ n, FaithfulTracialState (A n)),
        (∀ (n : ℕ) (v : A n), star v * v = 1 → v * star v = 1) →
        ∀ U : ∀ n, H → unitary (A n),
          (∀ g h : H, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
            ‖(U n (g * h) : A n) - (U n g : A n) * (U n h : A n)‖ ≤ ε) →
          ∀ x : ∀ n, A n,
            (∃ M : ℝ, 0 ≤ M ∧ ∀ n, ‖x n‖ ≤ M) →
            (∀ γ : Γ, TracialCommutatorVanishing A τ U x (iota γ)) →
            ∀ γ : Γ, TracialCommutatorVanishing A τ U
              (fun n ↦ (U n s : A n) * x n * star (U n s : A n)) (iota γ)

/-! ## The refuting coordinates: constant reduced group C⋆-algebras -/

namespace ConstantReduced

variable (E : Type) [Group E]

/-- The manuscript's refuting coordinates: every coordinate is the reduced
group C⋆-algebra of the ambient group, with no dependence on the index. -/
abbrev coord : ℕ → Type := fun _ ↦ ReducedGroupCStar E

/-- Every coordinate carries the canonical faithful tracial state. -/
def trace : ∀ n : ℕ, FaithfulTracialState (coord E n) :=
  fun _ ↦ canonicalFaithfulTracialState E

/-- Every coordinate is finite: an isometry is unitary.  This discharges the
stable-finiteness hypothesis of the candidate property, from the faithful
trace alone. -/
theorem isometry_unitary (n : ℕ) (v : coord E n) (hv : star v * v = 1) :
    v * star v = 1 :=
  (trace E n).mul_star_eq_one_of_star_mul_eq_one hv

/-- The left regular unitaries, constant in the coordinate. -/
def unitaries : ∀ n : ℕ, E → unitary (coord E n) :=
  fun _ g ↦ reducedLeftRegularUnitary E g

@[simp] theorem coe_unitaries (n : ℕ) (g : E) :
    ((unitaries E n g : coord E n)) = reducedLeftRegular E g := rfl

/-- The left regular unitaries are exactly multiplicative, so the asymptotic
multiplicativity hypothesis holds with defect zero. -/
theorem unitaries_almostMultiplicative (g h : E) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N,
      ‖((unitaries E n (g * h) : coord E n)) -
        ((unitaries E n g : coord E n)) * ((unitaries E n h : coord E n))‖ ≤ ε := by
  refine ⟨0, fun n _ ↦ ?_⟩
  simp only [coe_unitaries]
  rw [← reducedLeftRegular_mul, sub_self, norm_zero]
  exact hε.le

/-- A group element commuting with `g` has an exactly vanishing commutator in
every constant coordinate: the hypothesis on the transported element holds
with no analysis at all. -/
theorem tracialCommutatorVanishing_of_commute {c g : E} (h : Commute c g) :
    TracialCommutatorVanishing (coord E) (trace E) (unitaries E)
      (fun _ ↦ reducedLeftRegular E c) g := by
  intro ε hε
  refine ⟨0, fun n _ ↦ ?_⟩
  have hzero : reducedLeftRegular E c * ((unitaries E n g : coord E n)) -
      ((unitaries E n g : coord E n)) * reducedLeftRegular E c = 0 := by
    rw [coe_unitaries, ← reducedLeftRegular_mul, ← reducedLeftRegular_mul, h.eq,
      sub_self]
  show traceTwoNorm (trace E n)
      (reducedLeftRegular E c * ((unitaries E n g : coord E n)) -
        ((unitaries E n g : coord E n)) * reducedLeftRegular E c) ≤ ε
  rw [hzero, traceTwoNorm_zero]
  exact hε.le

/-- **Constant coordinates convert asymptotic vanishing into exact vanishing.**
Along a constant sequence there is nothing to converge to: a single coordinate
already sees every tolerance, and the trace is faithful. -/
theorem eq_zero_of_constantVanishing {H : Type} [Group H]
    (u : unitary (ReducedGroupCStar E)) (y : ReducedGroupCStar E)
    (U : ∀ n : ℕ, H → unitary (coord E n)) (x : ∀ n : ℕ, coord E n) (g : H)
    (hU : ∀ n : ℕ, U n g = u) (hx : ∀ n : ℕ, x n = y)
    (hvanish : TracialCommutatorVanishing (coord E) (trace E) U x g) :
    y * (u : ReducedGroupCStar E) - (u : ReducedGroupCStar E) * y = 0 := by
  refine eq_zero_of_traceTwoNorm_le (canonicalFaithfulTracialState E) ?_
  intro ε hε
  obtain ⟨N, hN⟩ := hvanish ε hε
  have hb := hN N le_rfl
  rw [hU N, hx N] at hb
  exact hb

/-- Conjugation of a left regular unitary is the left regular unitary of the
conjugate: this is the step that turns the transported coordinate element into
the transported group element `t c t⁻¹`. -/
theorem conj_reducedLeftRegular (t c : E) :
    reducedLeftRegular E t * reducedLeftRegular E c *
        star (reducedLeftRegular E t) =
      reducedLeftRegular E (t * c * t⁻¹) := by
  rw [star_reducedLeftRegular, ← reducedLeftRegular_mul, ← reducedLeftRegular_mul]

/-- The left regular representation is injective: the reduced group
C⋆-algebra sees the group exactly. -/
theorem reducedLeftRegular_injective :
    Function.Injective (reducedLeftRegular E) := by
  intro g h hgh
  have hu : reducedLeftRegularUnitary E g = reducedLeftRegularUnitary E h :=
    Subtype.ext hgh
  exact reducedLeftRegularUnitaryHom_injective E hu

end ConstantReduced

/-! ## The no-go theorem -/

open ConstantReduced

/-- **No faithfully traced coordinate transport theorem can hold.**  Any
Kazhdan compression core with a single nontrivial pointwise compression defect
refutes it, through the constant coordinates `A n = C⋆_r(E)`.

The proof is the manuscript's paragraph, line by line: feed the candidate
property the constant reduced coordinates, the left regular unitaries (exactly
multiplicative), and the root `c` (whose commutators with the Kazhdan image
are exactly zero); read the conclusion at one coordinate; and use faithfulness
of the canonical trace together with injectivity of the left regular
representation to move the collapse back into the group, where it contradicts
nontriviality of the defect. -/
theorem not_faithfullyTracedCoordinateTransport_of_core
    {Γ E : Type} [Group Γ] [Group E]
    (C : KazhdanCompressionCore Γ E)
    (hT : HasKazhdanPropertyTComplex.{0, w} Γ)
    (γ₀ : Γ) (hdefect : ⁅C.transported, C.iota γ₀⁆ ≠ 1) :
    ¬ FaithfullyTracedCoordinateTransport.{w} := by
  intro hTransport
  apply hdefect
  rw [commutatorElement_eq_one_iff_commute, commute_iff_eq]
  have hconc := hTransport Γ E hT C.iota C.t C.compresses
    (coord E) (trace E) (isometry_unitary E) (unitaries E)
    (unitaries_almostMultiplicative E)
    (fun _ ↦ reducedLeftRegular E C.c)
    ⟨‖reducedLeftRegular E C.c‖, norm_nonneg _, fun _ ↦ le_rfl⟩
    (fun γ ↦ tracialCommutatorVanishing_of_commute E (C.comm_c γ))
    γ₀
  have hkey :
      reducedLeftRegular E C.transported * reducedLeftRegular E (C.iota γ₀) -
        reducedLeftRegular E (C.iota γ₀) * reducedLeftRegular E C.transported = 0 :=
    eq_zero_of_constantVanishing E (reducedLeftRegularUnitary E (C.iota γ₀))
      (reducedLeftRegular E C.transported) (unitaries E)
      (fun n ↦ ((unitaries E n C.t : coord E n)) * reducedLeftRegular E C.c *
        star ((unitaries E n C.t : coord E n)))
      (C.iota γ₀) (fun _ ↦ rfl) (fun _ ↦ conj_reducedLeftRegular E C.t C.c) hconc
  rw [← reducedLeftRegular_mul, ← reducedLeftRegular_mul] at hkey
  exact reducedLeftRegular_injective E (sub_eq_zero.mp hkey)

/-! ## The manuscript's instance -/

/-- The distinguished pointwise compression defect of the literal group is
nontrivial, because its square is the literal mark. -/
theorem literal_compressionDefect_ne_one :
    LiteralNonMFEndpoint.compressionDefect ≠ 1 := by
  intro h
  apply LiteralNonMFEndpoint.compressionDefect_sq_ne_one
  rw [h, one_pow]

/-- **The limitations section's no-go, on the manuscript's own datum.**
Finite dimensionality of the coordinates cannot be traded for stable
finiteness together with faithful traces: the constant coordinates
`A n = C⋆_r(E)`, for the literal eight-generator group `E`, satisfy every
hypothesis of the candidate transport theorem and refute its conclusion. -/
theorem manuscriptFaithfullyTracedCoordinateNoGo :
    ¬ FaithfullyTracedCoordinateTransport.{w} :=
  not_faithfullyTracedCoordinateTransport_of_core
    LiteralNonMFEndpoint.inclusionData.toKazhdanCompressionCore
    (LiteralBaseP13PropertyTBridge.manuscriptBaseHasKazhdanPropertyT).2
    LiteralNonMFEndpoint.inclusionData.a
    literal_compressionDefect_ne_one

end

end FaithfullyTracedCoordinates
end GroupApproximation
