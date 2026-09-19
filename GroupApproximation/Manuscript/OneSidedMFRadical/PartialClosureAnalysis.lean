import GroupApproximation.Manuscript.OneSidedMFRadical.CentralCoronaCorner
import GroupApproximation.Manuscript.OneSidedMFRadical.FiniteDimensionalCommutant
import GroupApproximation.Manuscript.OneSidedMFRadical.PrintedLeavittEquations
import GroupApproximation.Manuscript.OneSidedMFRadical.SentenceOperativePureInfinitenessClosure
import GroupApproximation.Analysis.PolarLiftingPrintedSequence

/-!
# Printed sentences whose Lean attachment was only partial

A per-sentence audit of `non_mf_groups_exist.tex` graded a number of rows
`partial`: a declaration was attached, and it proved *part* of the printed
sentence, but a named clause of the print was carried by no declaration.  This
module closes six of those gaps.  Each entry is a named `Prop` whose
quantifiers and hypotheses all live *inside* the statement -- the shape
`#audit_closed_axioms` accepts, since it throws on any leading binder -- and a
theorem proving it.

Nothing here is a renaming of an existing declaration: in every case the
printed clause below was previously either inline inside somebody's proof, or
provable only under a hypothesis the print does not make.

## What is closed, and what the gap was

* **`thm:commutant`, "If `x ∈ C`, `h ∈ L`, and `h' = uhu⁻¹ ∈ L`, then …"**
  (`PrintedCommutantConjugationChain`).  The printed proof runs a three-line
  chain
  `ρ(h)ρ(u)⁻¹xρ(u) = ρ(u)⁻¹ρ(h')xρ(u) = ρ(u)⁻¹xρ(h')ρ(u) = ρ(u)⁻¹xρ(u)ρ(h)`.
  The repository reached the same *inclusion* through
  `Sofic/FreeLampRigidity.adjointRep_conj_fixed_iff`, so the chain itself was
  not a named step.  Here it is, one equality per printed line.

* **`thm:commutant`, "Thus `ρ(u)⁻¹Cρ(u) ⊆ C`."**
  (`PrintedCommutantConjugateInclusion`).  The inclusion previously appeared
  only as one direction of `inv_compressor_mem_commutantStabilizer`, an
  iff carrying a `[FiniteDimensional k V]` hypothesis.  The printed inclusion
  needs no finite dimensionality -- finite dimensionality is what the *next*
  printed sentence spends, to upgrade the inclusion to an equality -- and the
  statement below has none.

* **`lem:stable-finite`, "For all sufficiently large `n`, the matrix `x_n` is
  invertible, and the unitary `x_n(x_n^*x_n)^{-1/2}` differs from `x_n` by
  `o(1)`."**  (`PrintedOneSidedPolarCorrection`,
  `PrintedOneSidedUnitaryRepresentatives`).  `Analysis/PolarLiftingGeneralCStar`
  proves invertibility and unitarity of the polar correction from *both* Gram
  defects, because over an arbitrary unital `C*`-algebra that is what the
  Neumann series needs.  The printed sentence has only `x_n^*x_n → 1` at its
  disposal -- the hypothesis of `lem:stable-finite` is `v^*v = 1`, one-sided --
  and gets the two clauses from finite dimension instead.  Both clauses are
  proved below from the one-sided Gram bound alone, at matrix blocks:
  invertibility by the determinant, and `uu^* = 1` from `u^*u = 1` by
  Dedekind finiteness of a matrix algebra.

* **`lem:central-corona-corner`, "The commutation relation in the corona
  gives `‖q_nU_n(g) - U_n(g)q_n‖ → 0`."**
  (`PrintedCoronaCommutationVanishing`).  This was the inline `hcommCof` block
  of `manuscriptCentralCoronaCorner`, and every consumer downstream received
  it as the structure field `PrintedCornerData.commutator_vanishing`, i.e. as
  an assumption.  It is a standalone implication and is stated as one.

* **`lem:central-corona-corner`, "Consequently `q_nU_n(g)q_n`, viewed on
  `q_nℂ^{d_n}`, has *both* unitarity defects converging to zero."**
  (`PrintedBothCornerUnitarityDefects`).  Only `‖C^HC - 1‖ ≤ ‖[V,q]‖²` was
  proved (`norm_cornerGram_sub_one_le`), because the polar correction used
  downstream consumes only that one.  `norm_cornerCoGram_sub_one_le` below is
  the other half, with the same bound: it is the first estimate applied to
  `V^H`, whose commutator with `q` has the same norm.

* **"The binary Leavitt algebra is purely infinite simple."**
  (`PrintedBinaryLeavittPurelyInfiniteSimple`).  The tree carried
  `IsSimpleRing R` together with `HasSingleSandwichDivision R`, but had no
  pure-infiniteness predicate, so "purely infinite" was not a statement about
  `R` at all.  `IsPurelyInfiniteSimpleUnitalRing` is the standard predicate for
  a *unital simple* ring -- simple, not a division ring, and every nonzero
  element sandwiches to `1` -- and all three clauses are proved for `R`.  The
  new content is the middle clause, which is read off the Leavitt relations:
  `t₀s₀ = 1` while `s₀t₀ ≠ 1`, so `s₀` has a left inverse and is not a unit.

## What is *not* closed here, and why

Six rows of the same audit are untouched.  Two are literature citations that
the manuscript credits and does not prove (Preusser's normal-subgroup theorems
for linear groups over exchange rings; Ershov--Jaikin-Zapirain's property (T)
for `EL_n(R)`, `n ≥ 3`, over any finitely generated unital ring -- the tree has
only the binary Leavitt instance).  The remaining four need an ingredient that
is genuinely absent: an `ℓ²`-direct sum of the GNS family of
`Analysis/CStarStateGNS` (for "represent `B` faithfully and nondegenerately");
a diagonalisation producing a single model sequence from per-element `limsup`
positivity (for the converse of the Introduction's "equivalently"); the
corona-order-to-vector-inequality bridge in the corner (for the Kazhdan
inequality of `thm:normal-kazhdan`); and the identification of the corrected
corner Gram class with `unitaryGram` (for "represent `b`").  None of them is
faked below.

**Corrected 2026-08-25.  Two of those four are now closed**, and this paragraph
understated the repository until today:

* the converse of the Introduction's "equivalently" is
  `PrintedModelSeparationConverse.manuscriptPrintedMFModelSeparation`, a genuine
  `↔`;
* the corner Kazhdan inequality is
  `CorrectedCornerProjectionZero.manuscriptPrintedCorrectedCornerKazhdanDetection`,
  proved hypothesis-free and carried on the `#audit_closed_axioms` roster of
  `Endpoint/OneSidedTransportAudit.lean`.

Preusser's normal-subgroup theorems are also no longer only cited: both forms of
his Theorem 3 are proved in `Leavitt/PreusserNormalizedBy.lean` and
`Leavitt/PreusserLevelUniqueness.lean`.  Ershov--Jaikin-Zapirain is proved for
every rank `n ≥ 3` over every finite field
(`Steinberg/GeneralRankFiniteFieldPropertyT.lean`); characteristic zero remains
open.  What genuinely remains from the list above is the `ℓ²`-direct sum of the
GNS family, and the "represent `b`" identification.

## Manuscript status

Certifies six previously partial printed clauses.  No endpoint changes: every
theorem here is an addition to the printed-fidelity layer.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

open Filter Matrix
open PrintedCornerCompression
open KazhdanCornerMatrices
open RankTwelveEndpoint
open scoped Matrix.Norms.L2Operator

noncomputable section

/-! ## `thm:commutant`: the printed three-line chain, and the inclusion

`non_mf_groups_exist.tex`, the proof of `thm:commutant`:

> Put `C = ρ(L)'`.  If `x ∈ C`, `h ∈ L`, and `h' = uhu⁻¹ ∈ L`, then
> `ρ(h)ρ(u)⁻¹xρ(u) = ρ(u)⁻¹ρ(h')xρ(u) = ρ(u)⁻¹xρ(h')ρ(u) = ρ(u)⁻¹xρ(u)ρ(h)`.
> Thus `ρ(u)⁻¹Cρ(u) ⊆ C`.

Neither the chain nor the bare inclusion had a declaration: `FreeLampRigidity`
obtains the same containment from `adjointRep_conj_fixed_iff` under a
`[FiniteDimensional k V]` hypothesis, which the printed inclusion does not use.
-/

section Commutant

variable {G : Type*} {k : Type*} {V : Type*} [Group G] [Field k] [AddCommGroup V]
  [Module k V]

/-- Two representation values compose to the value at the product.  The
`adjointRep` analogue of this identity is `FreeLampRigidity.adjointRep_mul_apply`
and it is proved the same way. -/
theorem rho_apply_mul (rho : G →* (V ≃ₗ[k] V)) (a b : G) (v : V) :
    rho a (rho b v) = rho (a * b) v := by
  rw [map_mul, LinearEquiv.mul_eq_trans, LinearEquiv.trans_apply]

/-- `ρ(u⁻¹)⁻¹ = ρ(u)`, in applied form.  This is what identifies the adjoint
action of `u⁻¹` with the printed conjugation `z ↦ ρ(u)⁻¹zρ(u)`. -/
theorem rho_symm_inv_apply (rho : G →* (V ≃ₗ[k] V)) (u : G) (v : V) :
    (rho u⁻¹).symm v = rho u v := by
  rw [LinearEquiv.symm_apply_eq, rho_apply_mul, inv_mul_cancel, map_one,
    LinearEquiv.one_eq_refl, LinearEquiv.refl_apply]

/-- **The printed three-line chain of `thm:commutant`**, as three named
equalities of endomorphisms, in the printed order:

* `ρ(h)·(ρ(u)⁻¹xρ(u)) = ρ(u)⁻¹ρ(h')xρ(u)`  — the relation `hu⁻¹ = u⁻¹h'`;
* `ρ(u)⁻¹ρ(h')xρ(u) = ρ(u)⁻¹xρ(h')ρ(u)`   — `x` commutes with `ρ(h')`;
* `ρ(u)⁻¹xρ(h')ρ(u) = (ρ(u)⁻¹xρ(u))·ρ(h)` — the relation `h'u = uh`.

`ρ(u)⁻¹` is written `ρ(u⁻¹)`, which is the same endomorphism because `ρ` is a
homomorphism.  The hypothesis `x ∈ C` is spelled as the printed commutation
`ρ(ℓ)x = xρ(ℓ)` for `ℓ ∈ L`, and `h' = uhu⁻¹ ∈ L` is a hypothesis exactly as
printed.  Nothing about `V` is assumed beyond being a `k`-module. -/
def PrintedCommutantConjugationChain : Prop :=
  ∀ (G : Type) (k : Type) (V : Type) [Group G] [Field k] [AddCommGroup V]
      [Module k V] (rho : G →* (V ≃ₗ[k] V)) (L : Subgroup G) (u : G)
      (x : V →ₗ[k] V),
      (∀ ell ∈ L, (rho ell : V →ₗ[k] V) ∘ₗ x = x ∘ₗ (rho ell : V →ₗ[k] V)) →
      ∀ h ∈ L, u * h * u⁻¹ ∈ L →
        ((rho h : V →ₗ[k] V) ∘ₗ
              ((rho u⁻¹ : V →ₗ[k] V) ∘ₗ x ∘ₗ (rho u : V →ₗ[k] V))
            = (rho u⁻¹ : V →ₗ[k] V) ∘ₗ (rho (u * h * u⁻¹) : V →ₗ[k] V) ∘ₗ x
                ∘ₗ (rho u : V →ₗ[k] V)) ∧
        ((rho u⁻¹ : V →ₗ[k] V) ∘ₗ (rho (u * h * u⁻¹) : V →ₗ[k] V) ∘ₗ x
              ∘ₗ (rho u : V →ₗ[k] V)
            = (rho u⁻¹ : V →ₗ[k] V) ∘ₗ x ∘ₗ (rho (u * h * u⁻¹) : V →ₗ[k] V)
                ∘ₗ (rho u : V →ₗ[k] V)) ∧
        ((rho u⁻¹ : V →ₗ[k] V) ∘ₗ x ∘ₗ (rho (u * h * u⁻¹) : V →ₗ[k] V)
              ∘ₗ (rho u : V →ₗ[k] V)
            = ((rho u⁻¹ : V →ₗ[k] V) ∘ₗ x ∘ₗ (rho u : V →ₗ[k] V))
                ∘ₗ (rho h : V →ₗ[k] V))

/-- Closed proof of the printed three-line chain. -/
theorem manuscriptPrintedCommutantConjugationChain :
    PrintedCommutantConjugationChain := by
  intro G k V _ _ _ _ rho L u x hx h _hh hh'
  refine ⟨?_, ?_, ?_⟩
  · ext v
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [rho_apply_mul rho h u⁻¹, rho_apply_mul rho u⁻¹ (u * h * u⁻¹),
      show h * u⁻¹ = u⁻¹ * (u * h * u⁻¹) by group]
  · ext v
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    have happ : rho (u * h * u⁻¹) (x (rho u v)) = x (rho (u * h * u⁻¹) (rho u v)) := by
      have h2 := congrArg (fun T : V →ₗ[k] V ↦ T (rho u v)) (hx (u * h * u⁻¹) hh')
      simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe] using h2
    exact congrArg (fun w : V ↦ rho u⁻¹ w) happ
  · ext v
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    have hinner : rho (u * h * u⁻¹) (rho u v) = rho u (rho h v) := by
      rw [rho_apply_mul rho (u * h * u⁻¹) u, rho_apply_mul rho u h,
        show u * h * u⁻¹ * u = u * h by group]
    exact congrArg (fun w : V ↦ rho u⁻¹ (x w)) hinner

/-- **"Thus `ρ(u)⁻¹Cρ(u) ⊆ C`."**  Two forms of the same printed inclusion,
neither of which assumes finite dimensionality:

* the elementwise form — an endomorphism commuting with `ρ(L)` still commutes
  with `ρ(L)` after conjugation by `ρ(u)⁻¹`;
* the subspace form — the image of the commutant `C = fixedSubmodule (Ad ρ) L`
  under `Ad(ρ(u⁻¹))` is contained in `C`, together with the identification of
  `Ad(ρ(u⁻¹))z` with the printed conjugate `ρ(u)⁻¹zρ(u)`.

The printed hypothesis is `uLu⁻¹ ≤ L`, and that is the only hypothesis.
`Criterion/ExactCompression.fixedSubmodule_map_eq` states the *equality* of the
next printed sentence and needs `[FiniteDimensional k V]` for it; the
inclusion proved here is the step before finite dimension is spent. -/
def PrintedCommutantConjugateInclusion : Prop :=
  ∀ (G : Type) (k : Type) (V : Type) [Group G] [Field k] [AddCommGroup V]
      [Module k V] (rho : G →* (V ≃ₗ[k] V)) (L : Subgroup G) (u : G),
      (∀ ell ∈ L, u * ell * u⁻¹ ∈ L) →
        (∀ x : V →ₗ[k] V,
            (∀ ell ∈ L, (rho ell : V →ₗ[k] V) ∘ₗ x = x ∘ₗ (rho ell : V →ₗ[k] V)) →
            ∀ ell ∈ L,
              (rho ell : V →ₗ[k] V) ∘ₗ
                  ((rho u⁻¹ : V →ₗ[k] V) ∘ₗ x ∘ₗ (rho u : V →ₗ[k] V))
                = ((rho u⁻¹ : V →ₗ[k] V) ∘ₗ x ∘ₗ (rho u : V →ₗ[k] V))
                    ∘ₗ (rho ell : V →ₗ[k] V)) ∧
        (∀ z : V →ₗ[k] V,
            adjointRep rho u⁻¹ z
              = (rho u⁻¹ : V →ₗ[k] V) ∘ₗ z ∘ₗ (rho u : V →ₗ[k] V)) ∧
        (fixedSubmodule (adjointRep rho) L).map
            (adjointRep rho u⁻¹ : Module.End k (Module.End k V))
          ≤ fixedSubmodule (adjointRep rho) L

/-- Closed proof of "Thus `ρ(u)⁻¹Cρ(u) ⊆ C`." -/
theorem manuscriptPrintedCommutantConjugateInclusion :
    PrintedCommutantConjugateInclusion := by
  intro G k V _ _ _ _ rho L u hu
  refine ⟨?_, ?_, ?_⟩
  · intro x hx ell hell
    obtain ⟨e1, e2, e3⟩ :=
      manuscriptPrintedCommutantConjugationChain G k V rho L u x hx ell hell
        (hu ell hell)
    exact e1.trans (e2.trans e3)
  · intro z
    ext v
    simp only [adjointRep_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [rho_symm_inv_apply rho u v]
  · rintro y ⟨z, hz, rfl⟩
    refine mem_fixedSubmodule.mpr fun delta hdelta ↦ ?_
    exact (adjointRep_conj_fixed_iff rho u delta z).mp
      (mem_fixedSubmodule.mp hz _ (hu delta hdelta))

end Commutant

/-! ## `lem:stable-finite`: the one-sided polar correction at matrix blocks

`non_mf_groups_exist.tex`, the proof of `lem:stable-finite`:

> Suppose that `v^*v = 1` in the corona, and let `(x_n)` be a bounded lift of
> `v`.  Then `x_n^*x_n → 1` in norm.  For all sufficiently large `n`, the
> matrix `x_n` is invertible, and the unitary `x_n(x_n^*x_n)^{-1/2}` differs
> from `x_n` by `o(1)`.

The hypothesis is one-sided.  `Analysis/PolarLiftingGeneralCStar` proves the
same conclusions over an arbitrary unital `C*`-algebra, but from *both* Gram
defects, since `isUnit_of_norm_gram_lt` is a Neumann-series argument that needs
`xx^*` as well.  At matrix blocks the printed derivation is available: `x^*x`
invertible forces `det x ≠ 0`, and `u^*u = 1` forces `uu^* = 1`. -/

section MatrixPolar

/-- The bundled `C*`-algebra structure on one matrix block at the `L2` operator
norm.  Six field assignments, every one of them an instance already.  It is
`local` for the reason `Analysis/PolarLiftingMatrixBlocks` gives: `Matrix`
carries several norms in mathlib and they are scoped deliberately, so a global
registration would decide the choice for every file mentioning a matrix.  The
elaborated statements below carry the instance term with them. -/
local instance matrixBlockCStarAlgebra (Z : Type) [Fintype Z] [DecidableEq Z]
    [Nonempty Z] : CStarAlgebra (Matrix Z Z ℂ) where
  toNormedRing := inferInstance
  toStarRing := inferInstance
  toCompleteSpace := inferInstance
  toCStarRing := inferInstance
  toNormedAlgebra := inferInstance
  toStarModule := inferInstance

/-- **"the matrix `x_n` is invertible, and the unitary `x_n(x_n^*x_n)^{-1/2}`
differs from `x_n` by `o(1)`"**, at one block and from the printed *one-sided*
Gram hypothesis alone.

All three printed clauses -- invertibility, unitarity of the polar correction,
and the `o(1)` estimate -- follow from `‖x^*x - 1‖ ≤ 1/2`.  The estimate was
already one-sided (`norm_polarUnitary_sub_le`); the other two were not.

* Invertibility: `(x^*x)^{-1/2}(x^*x)(x^*x)^{-1/2} = 1` gives
  `det(x^*x) ∈ ℂˣ`, hence `det x ∈ ℂˣ`, hence `x` invertible.  This is the
  printed "by finite dimension", and it is where the matrix blocks differ from
  a general unital `C*`-algebra.
* Unitarity: `u^*u = 1` needs only the one-sided hypothesis, and `uu^* = 1`
  then follows because a matrix algebra over a commutative ring is
  Dedekind-finite (`mul_eq_one_comm`).

The statement is non-vacuously instantiable: `x = 1` satisfies the hypothesis
at every nonempty `Z`, and so does every unitary matrix. -/
def PrintedOneSidedPolarCorrection : Prop :=
  ∀ (Z : Type) [Fintype Z] [DecidableEq Z] [Nonempty Z] (x : Matrix Z Z ℂ),
    ‖star x * x - 1‖ ≤ 1 / 2 →
      IsUnit x ∧
        PolarLiftingGeneralCStar.polarUnitary x ∈ unitary (Matrix Z Z ℂ) ∧
        ‖PolarLiftingGeneralCStar.polarUnitary x - x‖
          ≤ 2 * ‖x‖ * ‖star x * x - 1‖

/-- Closed proof of the one-sided polar correction at one matrix block. -/
theorem manuscriptPrintedOneSidedPolarCorrection :
    PrintedOneSidedPolarCorrection := by
  intro Z _ _ _ x hx
  have hpin : PolarLiftingGeneralCStar.polarInvSqrt x * (star x * x) *
      PolarLiftingGeneralCStar.polarInvSqrt x = 1 :=
    PolarLiftingGeneralCStar.polarInvSqrt_gram_polarInvSqrt hx
  have hdet : (PolarLiftingGeneralCStar.polarInvSqrt x).det * (star x * x).det *
      (PolarLiftingGeneralCStar.polarInvSqrt x).det = 1 := by
    rw [← Matrix.det_mul, ← Matrix.det_mul, hpin, Matrix.det_one]
  have hdetgram : IsUnit ((star x * x).det) := by
    refine isUnit_iff_exists_inv.mpr
      ⟨(PolarLiftingGeneralCStar.polarInvSqrt x).det *
        (PolarLiftingGeneralCStar.polarInvSqrt x).det, ?_⟩
    calc (star x * x).det * ((PolarLiftingGeneralCStar.polarInvSqrt x).det *
          (PolarLiftingGeneralCStar.polarInvSqrt x).det)
        = (PolarLiftingGeneralCStar.polarInvSqrt x).det * (star x * x).det *
            (PolarLiftingGeneralCStar.polarInvSqrt x).det := by ring
      _ = 1 := hdet
  have hxu : IsUnit x := by
    rw [Matrix.isUnit_iff_isUnit_det]
    rw [Matrix.det_mul] at hdetgram
    exact isUnit_of_mul_isUnit_right hdetgram
  have hcu : IsUnit (PolarLiftingGeneralCStar.polarInvSqrt x) :=
    PolarLiftingGeneralCStar.isUnit_polarInvSqrt hx
  have hsa : IsSelfAdjoint (PolarLiftingGeneralCStar.polarInvSqrt x) :=
    PolarLiftingGeneralCStar.polarInvSqrt_isSelfAdjoint x
  have hu : IsUnit (PolarLiftingGeneralCStar.polarUnitary x) := hxu.mul hcu
  refine ⟨hxu, hu.mem_unitary_of_star_mul_self ?_,
    PolarLiftingGeneralCStar.norm_polarUnitary_sub_le hx⟩
  calc star (PolarLiftingGeneralCStar.polarUnitary x) *
        PolarLiftingGeneralCStar.polarUnitary x
      = star (x * PolarLiftingGeneralCStar.polarInvSqrt x) *
          (x * PolarLiftingGeneralCStar.polarInvSqrt x) := rfl
    _ = PolarLiftingGeneralCStar.polarInvSqrt x * (star x * x) *
          PolarLiftingGeneralCStar.polarInvSqrt x := by
        rw [star_mul, hsa.star_eq]
        simp only [mul_assoc]
    _ = 1 := hpin

/-- **"Thus `v` is represented by unitaries"**, at the level of the printed
lift and from the printed one-sided hypothesis.

`v^*v = 1` in the corona says exactly that a lift `(x_n)` has
`‖x_n^*x_n - 1‖ → 0`, and the conclusion is the printed one: there is a
coordinatewise *unitary* sequence at operator-norm distance `o(1)` from
`(x_n)`.  The witness is the printed one, `u_n = x_n(x_n^*x_n)^{-1/2}` where
the Gram defect allows it and `1` at the finitely many remaining indices --
the device `lem:lift` itself uses.

This is weaker than the printed sentence in one respect, stated here rather
than hidden: it is the statement about the lift, not about the corona class.
The step from "a coordinatewise unitary sequence at distance `o(1)` from a lift
of `v`" to "`v` is the class of that sequence" is the definition of the corona
quotient and is not carried below. -/
def PrintedOneSidedUnitaryRepresentatives : Prop :=
  ∀ (Z : ℕ → Type) [∀ n, Fintype (Z n)] [∀ n, DecidableEq (Z n)]
      [∀ n, Nonempty (Z n)] (x : ∀ n, Matrix (Z n) (Z n) ℂ),
      Tendsto (fun n ↦ ‖star (x n) * x n - 1‖) cofinite (nhds 0) →
        ∃ u : ∀ n, Matrix (Z n) (Z n) ℂ,
          (∀ n, u n ∈ unitary (Matrix (Z n) (Z n) ℂ)) ∧
          Tendsto (fun n ↦ ‖u n - x n‖) cofinite (nhds 0)

/-- Closed proof of "`v` is represented by unitaries", in lift form. -/
theorem manuscriptPrintedOneSidedUnitaryRepresentatives :
    PrintedOneSidedUnitaryRepresentatives := by
  intro Z _ _ _ x hx
  have hgood : ∀ᶠ n in cofinite, ‖star (x n) * x n - 1‖ ≤ 1 / 2 := by
    have hd := (Metric.tendsto_nhds.mp hx) ((1 : ℝ) / 2) (by norm_num)
    filter_upwards [hd] with n hn
    simpa only [Real.dist_eq, sub_zero, abs_norm] using hn.le
  refine ⟨fun n ↦ if ‖star (x n) * x n - 1‖ ≤ 1 / 2 then
      PolarLiftingGeneralCStar.polarUnitary (x n) else 1, ?_, ?_⟩
  · intro n
    show (if ‖star (x n) * x n - 1‖ ≤ 1 / 2 then
        PolarLiftingGeneralCStar.polarUnitary (x n) else 1)
      ∈ unitary (Matrix (Z n) (Z n) ℂ)
    by_cases hn : ‖star (x n) * x n - 1‖ ≤ 1 / 2
    · rw [if_pos hn]
      exact (manuscriptPrintedOneSidedPolarCorrection (Z n) (x n) hn).2.1
    · rw [if_neg hn]
      exact Submonoid.one_mem _
  · refine squeeze_zero' (g := fun n ↦ 4 * ‖star (x n) * x n - 1‖)
      (Eventually.of_forall fun n ↦ norm_nonneg _) ?_ ?_
    · filter_upwards [hgood] with n hn
      show ‖(if ‖star (x n) * x n - 1‖ ≤ 1 / 2 then
          PolarLiftingGeneralCStar.polarUnitary (x n) else 1) - x n‖
        ≤ 4 * ‖star (x n) * x n - 1‖
      rw [if_pos hn]
      have hxn : ‖x n‖ ≤ 2 := FiniteBlockCorona.norm_le_two_of_gram_le hn
      have hd : ‖PolarLiftingGeneralCStar.polarUnitary (x n) - x n‖
          ≤ 2 * ‖x n‖ * ‖star (x n) * x n - 1‖ :=
        PolarLiftingGeneralCStar.norm_polarUnitary_sub_le hn
      have hprod : 0 ≤ (2 - ‖x n‖) * ‖star (x n) * x n - 1‖ :=
        mul_nonneg (by linarith) (norm_nonneg _)
      nlinarith [hd]
    · simpa using hx.const_mul (4 : ℝ)

end MatrixPolar

/-! ## `lem:central-corona-corner`: the two printed sentences of the corner step

> The commutation relation in the corona gives
> `‖q_nU_n(g) - U_n(g)q_n‖ → 0`.  Consequently `q_nU_n(g)q_n`, viewed on
> `q_nℂ^{d_n}`, has both unitarity defects converging to zero.
-/

section Corner

/-- **"The commutation relation in the corona gives `‖q_nU_n(g) - U_n(g)q_n‖ → 0`."**

A standalone implication: if two bounded matrix sequences commute *after*
passing to the norm-matrix corona, their coordinate commutators vanish in
operator norm along `cofinite`.

Previously this was the inline `hcommCof` block inside the proof of
`manuscriptCentralCoronaCorner` (`CentralCoronaCorner.lean`), and downstream it
travelled as the structure field `PrintedCornerData.commutator_vanishing`, i.e.
as an assumption for every consumer.  The hypothesis is exactly the printed
"commutation relation in the corona", with no group and no representation in
sight: it is a fact about the quotient by the operator-norm null ideal.

Non-vacuously instantiable in both trivial and nontrivial ways: `a = b`
satisfies the hypothesis, and `manuscriptCentralCoronaCorner`'s central
projection supplies the printed instance. -/
def PrintedCoronaCommutationVanishing : Prop :=
  ∀ (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]
    (a b : BoundedMatrixSequence (fun n ↦ X n)),
    normMatrixCStarCoronaMk (fun n ↦ X n) a *
          normMatrixCStarCoronaMk (fun n ↦ X n) b
        = normMatrixCStarCoronaMk (fun n ↦ X n) b *
          normMatrixCStarCoronaMk (fun n ↦ X n) a →
      Tendsto (fun n ↦
        ‖(a : ∀ n, Matrix (X n) (X n) ℂ) n * (b : ∀ n, Matrix (X n) (X n) ℂ) n
          - (b : ∀ n, Matrix (X n) (X n) ℂ) n *
            (a : ∀ n, Matrix (X n) (X n) ℂ) n‖) cofinite (nhds 0)

/-- Closed proof of the printed corona-commutation sentence. -/
theorem manuscriptPrintedCoronaCommutationVanishing :
    PrintedCoronaCommutationVanishing := by
  intro X _ a b hcomm
  -- `normMatrixCStarCoronaMk` is a bare `→+*`, so the three hom identities are
  -- taken as fully applied terms, with the hom named: a bare `rw [map_sub]`
  -- leaves `F`, the source and the target as metavariables and its
  -- `AddMonoidHomClass` side condition cannot then be synthesised.  Stating
  -- each identity with the corona multiplication as this file writes it also
  -- keeps `hcomm` syntactically applicable to the result.
  have hexp : normMatrixCStarCoronaMk (fun n ↦ X n) (a * b - b * a)
      = normMatrixCStarCoronaMk (fun n ↦ X n) (a * b)
        - normMatrixCStarCoronaMk (fun n ↦ X n) (b * a) :=
    map_sub (normMatrixCStarCoronaMk (fun n ↦ X n)) (a * b) (b * a)
  have hab : normMatrixCStarCoronaMk (fun n ↦ X n) (a * b)
      = normMatrixCStarCoronaMk (fun n ↦ X n) a *
        normMatrixCStarCoronaMk (fun n ↦ X n) b :=
    map_mul (normMatrixCStarCoronaMk (fun n ↦ X n)) a b
  have hba : normMatrixCStarCoronaMk (fun n ↦ X n) (b * a)
      = normMatrixCStarCoronaMk (fun n ↦ X n) b *
        normMatrixCStarCoronaMk (fun n ↦ X n) a :=
    map_mul (normMatrixCStarCoronaMk (fun n ↦ X n)) b a
  have hzero : normMatrixCStarCoronaMk (fun n ↦ X n) (a * b - b * a) = 0 := by
    rw [hexp, hab, hba]
    exact sub_eq_zero_of_eq hcomm
  have hnull : Tendsto (fun n ↦
      ‖((a * b - b * a : BoundedMatrixSequence (fun n ↦ X n)) :
          ∀ n, Matrix (X n) (X n) ℂ) n‖) cofinite (nhds 0) :=
    (normMatrixCStarCoronaMk_eq_zero_iff (fun n ↦ X n) _).mp hzero
  refine hnull.congr' (Eventually.of_forall fun n ↦ ?_)
  rw [PrintedCornerRelabelling.commutator_coord X a b n]

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

/-- **The *other* unitarity defect of a compressed unitary.**
`Analysis/PrintedCornerCompression.norm_cornerGram_sub_one_le` bounds
`‖C^HC - 1‖` by the square of the printed commutator, where `C = q V q` read in
the corner coordinates.  This is the companion bound for `‖CC^H - 1‖`, with the
same right-hand side.

The proof is the printed symmetry and nothing else: `C^H` is the compression of
`V^H`, which is again an isometry because a square matrix with `V^HV = 1`
satisfies `VV^H = 1`, and `‖V^Hq - qV^H‖ = ‖Vq - qV‖` because the two
commutators are negatives of each other's conjugate transpose. -/
theorem norm_cornerCoGram_sub_one_le {q : Matrix Y Y ℂ} (hq : q.IsHermitian)
    (hidem : q * q = q) {V : Matrix Y Y ℂ} (hV : Vᴴ * V = 1) :
    ‖cornerCompression hq V * (cornerCompression hq V)ᴴ - 1‖
      ≤ ‖V * q - q * V‖ ^ 2 := by
  have hVV : V * Vᴴ = 1 := _root_.mul_eq_one_comm.mp hV
  have hV' : (Vᴴ)ᴴ * Vᴴ = 1 := by
    rw [Matrix.conjTranspose_conjTranspose]
    exact hVV
  have hkey := norm_cornerGram_sub_one_le hq hidem hV'
  have hadj : (cornerCompression hq Vᴴ)ᴴ = cornerCompression hq V := by
    simp only [cornerCompression]
    rw [principalBlock_conjTranspose, eigenbasisConj_conjTranspose,
      Matrix.conjTranspose_conjTranspose]
  have hadj2 : cornerCompression hq Vᴴ = (cornerCompression hq V)ᴴ := by
    rw [← hadj, Matrix.conjTranspose_conjTranspose]
  have hgram : cornerGram (cornerCompression hq Vᴴ)
      = cornerCompression hq V * (cornerCompression hq V)ᴴ := by
    simp only [cornerGram]
    rw [hadj2, Matrix.conjTranspose_conjTranspose]
  have hcomm : ‖Vᴴ * q - q * Vᴴ‖ = ‖V * q - q * V‖ := by
    have hqH : qᴴ = q := hq
    have hrw : Vᴴ * q - q * Vᴴ = -((V * q - q * V)ᴴ) := by
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_mul, hqH]
      abel
    rw [hrw, norm_neg, Matrix.l2_opNorm_conjTranspose]
  rw [← hgram, ← hcomm]
  exact hkey

/-- **"Consequently `q_nU_n(g)q_n`, viewed on `q_nℂ^{d_n}`, has both unitarity
defects converging to zero."**  Both printed defects, for every group element,
from the data the printed relabelling supplies.

Only the first of the two was previously bounded, because the polar correction
`polarCorrectUnitary` used downstream consumes only `C^HC`; the second printed
half was therefore unformalized.  Both are now bounded by the square of the
printed commutator norm, which vanishes by `PrintedCornerData.commutator_vanishing`.

Non-vacuously instantiable: `manuscriptCentralCoronaCorner` produces a
`PrintedCornerData` from a nonzero central projection of a countable
norm-matrix-corona representation. -/
def PrintedBothCornerUnitarityDefects : Prop :=
  ∀ (G : Type) [Group G] (model : ℕ → FiniteModel)
    (D : PrintedCornerData G model) (g : G),
      Tendsto (fun n ↦ ‖(D.compress n g)ᴴ * D.compress n g - 1‖)
        atTop (nhds 0) ∧
      Tendsto (fun n ↦ ‖D.compress n g * (D.compress n g)ᴴ - 1‖)
        atTop (nhds 0)

/-- Closed proof that both printed unitarity defects of the corner compression
converge to zero. -/
theorem manuscriptPrintedBothCornerUnitarityDefects :
    PrintedBothCornerUnitarityDefects := by
  intro G _ model D gel
  have hsq : Tendsto (fun n ↦ (D.commutatorNorm n gel) ^ 2) atTop (nhds 0) := by
    have hp := (D.commutatorNorm_tendsto gel).pow 2
    simpa using hp
  constructor
  · refine squeeze_zero' (g := fun n ↦ (D.commutatorNorm n gel) ^ 2)
      (Eventually.of_forall fun n ↦ norm_nonneg _)
      (Eventually.of_forall fun n ↦ ?_) hsq
    show ‖(D.compress n gel)ᴴ * D.compress n gel - 1‖ ≤ (D.commutatorNorm n gel) ^ 2
    exact D.norm_cornerGram_compress_le n gel
  · refine squeeze_zero' (g := fun n ↦ (D.commutatorNorm n gel) ^ 2)
      (Eventually.of_forall fun n ↦ norm_nonneg _)
      (Eventually.of_forall fun n ↦ ?_) hsq
    show ‖D.compress n gel * (D.compress n gel)ᴴ - 1‖ ≤ (D.commutatorNorm n gel) ^ 2
    exact norm_cornerCoGram_sub_one_le (D.qHermitian n) (D.qIdem n)
      (D.V_conjTranspose_mul_self n gel)

end Corner

/-! ## "The binary Leavitt algebra is purely infinite simple"

`non_mf_groups_exist.tex`:

> The binary Leavitt algebra is purely infinite simple~\cite{AbramsAranda},
> hence an exchange ring~\cite{AraExchange}, and its center is the base
> field~\cite{ArandaCrow}.

The exchange and centre clauses are exact in the tree
(`BinaryLeavitt.hasRightExchange`, `BinaryLeavitt.center_eq_bot`).  "Purely
infinite simple" was carried only as `IsSimpleRing R` together with
`HasSingleSandwichDivision R`, with no pure-infiniteness predicate anywhere, so
the printed adjective named nothing. -/

section PurelyInfinite

/-- **Purely infinite simple, for a unital ring.**  The standard predicate: the
ring is simple, it is not a division ring, and every nonzero element sandwiches
to the unit.  For a *unital simple* ring these three clauses are the definition
of pure infiniteness; the third alone is the fragment
`RankTwelveEndpoint.OperativePureInfinitenessInput` already isolates, and the
second is what distinguishes pure infiniteness from the trivial case of a
division ring, where the third clause also holds. -/
def IsPurelyInfiniteSimpleUnitalRing (S : Type*) [Ring S] : Prop :=
  IsSimpleRing S ∧ (¬ ∀ a : S, a ≠ 0 → IsUnit a) ∧
    ∀ a : S, a ≠ 0 → ∃ x y : S, x * a * y = 1

/-- **"The binary Leavitt algebra is purely infinite simple."**  The printed
adjective, on the concrete manuscript coefficient ring `R = L_{𝔽₂}(1,2)`. -/
def PrintedBinaryLeavittPurelyInfiniteSimple : Prop :=
  IsPurelyInfiniteSimpleUnitalRing R

/-- Closed proof that the binary Leavitt algebra is purely infinite simple.

Simplicity and the sandwich clause are already in the tree.  The middle clause
-- `R` is not a division ring -- is proved from the printed Leavitt relations:
`t₀s₀ = 1` while `s₀t₀ ≠ 1`, so `s₀` is a nonzero element with a left inverse
and no right inverse, hence not a unit. -/
theorem manuscriptPrintedBinaryLeavittPurelyInfiniteSimple :
    PrintedBinaryLeavittPurelyInfiniteSimple := by
  refine ⟨coefficientRing_isSimple, ?_, coefficientRing_hasSingleSandwichDivision⟩
  intro hdiv
  have hts : leavittFamily.t0 * leavittFamily.s0 = 1 := leavittFamily.t0_s0
  have hp : leavittFamily.s0 * leavittFamily.t0 ≠ 1 := by
    rw [← printed_p_eq]
    exact printed_p0_ne_one
  have hs0 : leavittFamily.s0 ≠ 0 := by
    intro h0
    have hzero : (0 : R) = 1 := by
      rw [← hts, h0, mul_zero]
    exact hp (by rw [h0, zero_mul]; exact hzero)
  obtain ⟨u, hu⟩ := hdiv leavittFamily.s0 hs0
  refine hp ?_
  have hstep : leavittFamily.t0 = ((u⁻¹ : Rˣ) : R) := by
    calc leavittFamily.t0
        = leavittFamily.t0 * (leavittFamily.s0 * ((u⁻¹ : Rˣ) : R)) := by
          rw [← hu, u.mul_inv, mul_one]
      _ = leavittFamily.t0 * leavittFamily.s0 * ((u⁻¹ : Rˣ) : R) := by
          rw [mul_assoc]
      _ = ((u⁻¹ : Rˣ) : R) := by rw [hts, one_mul]
  rw [hstep, ← hu]
  exact u.mul_inv

end PurelyInfinite

end

end OneSidedMFRadical
end Manuscript
end GroupApproximation
