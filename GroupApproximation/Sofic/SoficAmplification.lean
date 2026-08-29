import GroupApproximation.Sofic.SoficPositiveControl
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Amplification: the separation constant in `IsSofic` is not a convention

`IsSofic` requires distinct elements of the test set to be separated to within
`1 - ε`, with the same `ε` that bounds the multiplicative error.  The textbook
alternative fixes the separation at some constant `δ > 0` -- typically `1/4`,
or `1/2` -- and lets only the multiplicative error shrink.  The two are
equivalent, so `¬ IsSofic` refutes every one of these conventions at once and
not merely the sharp one.

The mechanism is the tensor power.  `powerPerm k p` acts on `Fin k → Y`
coordinatewise by `p`; two such powers disagree at a tuple exactly when their
factors disagree at some coordinate, so the agreement set is a full product and

  `hammingDistance (powerPerm k p) (powerPerm k q) = 1 - (1 - hammingDistance p q) ^ k`

(`hammingDistance_powerPerm`).  Passing to a power drives a fixed separation
`δ` up to `1 - (1 - δ) ^ k`, which beats any prescribed `1 - ε` once `k` is
large, while it inflates a multiplicative error `d` only to
`1 - (1 - d) ^ k ≤ k * d`, which is repaired by asking the weak hypothesis for
accuracy `ε / k` in the first place.  The exponent depends on `δ` and `ε`
alone, so the argument is uniform in the test set.

Main results:

* `hammingDistance_powerPerm` -- the exact power law for the distance.
* `isSofic_of_isSoficWeak` -- a fixed positive separation suffices.
* `isSofic_iff_weak` -- the two definitions agree, for every `δ ∈ (0, 1)`.
* `isSofic_iff_weakLocal` -- and with no side condition at all once `δ` is
  allowed to depend on the test set, which is the form
  `Sofic.SoficUltraproduct` needs.

These results prove internally that the fixed-separation and sharp-separation
definitions agree.
-/

/-! ## The tensor power of a permutation -/

/-! ## Models with a fixed separation constant -/
