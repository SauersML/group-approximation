import GroupApproximation.Analysis.LancePositiveDefinite
import GroupApproximation.Analysis.NuclearityAmenability

/-!
# The Lance debt, reduced to the compression statement

## What this module does

`NuclearityAmenability.reducedGroupCStar_not_nuclear_of_lance` consumes
Lance's theorem whole, as the hypothesis

> `lance : ∀ G, NuclearReduced G → HasInvariantMean G`.

The Lance lane (`LanceReiterMean`, `LancePositiveDefinite`) has now proved,
unconditionally, the entire analytic second half of the standard proof of
that hypothesis: unit `ℓ²`-vectors with translation coefficients near `1`
on prescribed finite sets yield an invariant mean
(`hasInvariantMean_of_coefficients_near_one`, via Reiter's condition and a
weak-* ultrafilter limit).

What remains of Lance's direction is exactly the **compression statement**:
from nuclearity of `C*_λ(G)` — the completely positive approximation
property of the reduced algebra — produce such almost-`1` coefficient
vectors.  In the textbook proof this is Stinespring dilation of the CP
approximants composed with the canonical trace.  Nothing in this
repository proves it, and this module does not pretend to: it records the
reduction

>  compression  ⟹  lance,

so that the standing hypothesis on the manuscript's nonnuclearity
paragraph is now the *smaller* statement.  Anyone who later formalizes the
compression step gets the paragraph's conclusion with no further work:
`reducedGroupCStar_not_nuclear_of_compression` below is the composite,
stated at the manuscript's literal group.

## Trust surface

Both declarations here are conditional and are marked so by their explicit
hypothesis binders, exactly like the `lance` hypothesis they refine.  The
quantifier placement again carries the weight: `compression` ranges over
*all* discrete groups while the final conclusion is about `E` alone, so the
premise cannot be discharged by an assumption tailored to `E`.  Nothing
may badge these from the manuscript, and the
`check_non_mf_unconditional.py` caveat recorded in
`NuclearityAmenability.lean` applies verbatim: a hypothesised predicate of
this shape is invisible to the structural rule and needs hand-written
treatment in the conditionality register.

## Manuscript status

`RE.05` remains conditional on Lance (`literature-input`), with the debt
now narrowed from "Lance's theorem" to "the CPAP-to-coefficients
compression".  No badge points here.
-/

namespace GroupApproximation
namespace LanceAmenability

/-- **The reduction of Lance's arrow.**  Given the compression statement —
nuclearity of the reduced algebra produces unit `ℓ²`-vectors with
translation coefficients uniformly near `1` on any prescribed finite set —
every group whose reduced algebra is nuclear carries an invariant mean.
The analytic half is the premise-free
`hasInvariantMean_of_coefficients_near_one`. -/
theorem hasInvariantMean_of_nuclearReduced
    (NuclearReduced : ∀ (H : Type) [Group H], Prop)
    (compression : ∀ (H : Type) [Group H], NuclearReduced H →
      ∀ (F : Finset H) (ε : ℝ), 0 < ε →
        ∃ ξ : H →₀ ℂ, l2NormSq ξ = 1 ∧
          ∀ g ∈ F, 1 - ε ≤ (coeffFn ξ g).re) :
    ∀ (H : Type) [Group H], NuclearReduced H →
      Amenability.HasInvariantMean H := by
  intro H _ hnuc
  exact hasInvariantMean_of_coefficients_near_one (compression H hnuc)

/-- **The manuscript's nonnuclearity conclusion, conditional on the
compression statement alone.**  This is
`NuclearityAmenability.reducedGroupCStar_not_nuclear_of_lance` with its
`lance` hypothesis discharged from the smaller `compression` premise: the
Reiter and coefficient halves of Lance's proof are no longer assumed. -/
theorem reducedGroupCStar_not_nuclear_of_compression
    (NuclearReduced : ∀ (H : Type) [Group H], Prop)
    (compression : ∀ (H : Type) [Group H], NuclearReduced H →
      ∀ (F : Finset H) (ε : ℝ), 0 < ε →
        ∃ ξ : H →₀ ℂ, l2NormSq ξ = 1 ∧
          ∀ g ∈ F, 1 - ε ≤ (coeffFn ξ g).re) :
    ¬ NuclearReduced LiteralNonMFPresentation.MarkedGroup :=
  NuclearityAmenability.reducedGroupCStar_not_nuclear_of_lance
    NuclearReduced
    (hasInvariantMean_of_nuclearReduced NuclearReduced compression)

end LanceAmenability
end GroupApproximation
