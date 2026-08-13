import GroupApproximation.Sofic.MarkedCompressionData
import GroupApproximation.Sofic.UnitaryProjectionBalance

/-!
# The marked Kazhdan-compression kill theorem

This file is the analytic endpoint of the operator-norm obstruction.  Given
`MarkedCompressionData Γ E`, the marked central involution

`w = [t c t⁻¹, (ι a) (t c t⁻¹) (ι a)⁻¹]`

is killed by every homomorphism from `E` to an operator-norm matrix
ultraproduct.

The finite-stage ingredients used by the proof are already available in the
repository:

* `ApproxInvolutionCorner` rounds the image of `w` and isolates its negative
  spectral sector without losing a small-rank corner;
* `KazhdanCornerCompression` constructs the moving Kazhdan spectral cut for
  the adjoint representation of `Γ`;
* `hsNormSq_unitary_projection_balance` says that a finite unitary has equal
  leakage in both directions across that cut.

The only remaining proof hole below is the assembly of these three finite
stage estimates for a *general ultrafilter-indexed* matrix ultraproduct.  In
particular, it is not a hidden group-theoretic or C*-algebraic assumption:
the hole has the exact conclusion consumed by `NormMFInvisible`, and all its
hypotheses are fields of `MarkedCompressionData` plus the concrete target
`UniversalWeakMF U X`.
-/

namespace GroupApproximation

open scoped commutatorElement

universe u

namespace MarkedCompressionData

variable {Γ : Type} {E : Type u} [Group Γ] [Group E]

/-- The image of the marked word remains an involution in every target
group.  This is the algebraic input to negative-sector rounding. -/
theorem map_word_pow_two (D : MarkedCompressionData Γ E)
    {H : Type*} [Group H] (rho : E →* H) :
    rho D.word ^ 2 = 1 := by
  rw [← map_pow, D.word_pow_two, map_one]

/-- The image of the marked word remains central in the image of `E`. -/
theorem map_word_commute (D : MarkedCompressionData Γ E)
    {H : Type*} [Group H] (rho : E →* H) (g : E) :
    Commute (rho D.word) (rho g) := by
  exact (D.word_commute g).map rho

/-- The compressor relation transported through an arbitrary
homomorphism. -/
theorem map_compress (D : MarkedCompressionData Γ E)
    {H : Type*} [Group H] (rho : E →* H) (γ : Γ) :
    rho D.t * rho (D.iota γ) * (rho D.t)⁻¹ =
      rho (D.iota (D.alpha γ)) := by
  simpa only [map_mul, map_inv] using congrArg rho (D.compress γ)

/-- Inclusion-only form of `map_compress`.  The analytic argument consumes
only the fact that conjugation by `t` carries the `Γ`-image back into itself;
it never uses multiplication properties of `alpha`.  This formulation is the
one to retain when `MarkedCompressionData` is generalized from a named
endomorphism to a bare one-sided subgroup compression. -/
theorem map_compresses (D : MarkedCompressionData Γ E)
    {H : Type*} [Group H] (rho : E →* H) (γ : Γ) :
    ∃ δ : Γ,
      rho D.t * rho (D.iota γ) * (rho D.t)⁻¹ = rho (D.iota δ) := by
  exact ⟨D.alpha γ, D.map_compress rho γ⟩

/-- The lamp-centralizer relation transported through an arbitrary
homomorphism. -/
theorem map_comm_c (D : MarkedCompressionData Γ E)
    {H : Type*} [Group H] (rho : E →* H) (γ : Γ) :
    Commute (rho D.c) (rho (D.iota γ)) := by
  exact (D.comm_c γ).map rho

/-- **Analytic marked-compression kill.**  Every operator-norm matrix
ultraproduct representation kills the marked central involution.

The unfinished block is a single, sharply delimited finite-stage assembly:
round `rho D.word`, cut to its negative sector, apply the Kazhdan spectral
projection to the adjoint `Γ`-microstates, use `D.compress` for one-sided
leakage and `hsNormSq_unitary_projection_balance` for the reverse leakage,
then use `D.comm_c` to make the marked commutator Hilbert--Schmidt trivial.
On the negative sector the rounded word is `-1`, giving the contradiction.

No nontriviality hypothesis on `D.word` belongs here; nontriviality is used
only afterwards to conclude `¬ IsWeakMF E`. -/
theorem word_normMFInvisible (D : MarkedCompressionData Γ E) :
    NormMFInvisible D.word := by
  intro I U X rho
  -- ANALYTIC GAP: ultrafilter-indexed finite-stage Kazhdan/negative-corner
  -- assembly described in the theorem docstring.
  sorry

/-- Package the analytic theorem together with a separately supplied
nontriviality witness.  This cleanly separates the infinite Clifford witness
(`D.word ≠ 1`) from the finite-matrix sterility theorem above. -/
def normCertificate (D : MarkedCompressionData Γ E)
    (hne : D.word ≠ 1) : MarkedCompressionNormCertificate E where
  t := D.t
  a := D.iota D.a
  c := D.c
  witness_ne_one := hne
  witness_invisible := D.word_normMFInvisible

/-- A countable marked-compression group with nontrivial marked word is not
weak/operator-norm MF. -/
theorem not_isWeakMF [Countable E] (D : MarkedCompressionData Γ E)
    (hne : D.word ≠ 1) : ¬ IsWeakMF E :=
  (D.normCertificate hne).not_isWeakMF

end MarkedCompressionData

end GroupApproximation
