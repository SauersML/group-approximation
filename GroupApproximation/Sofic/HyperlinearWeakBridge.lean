import GroupApproximation.Sofic.HyperlinearNonScalar
import GroupApproximation.Sofic.HyperlinearReduction
import GroupApproximation.Sofic.HyperlinearScalar
import GroupApproximation.Sofic.NormTraceGap

/-!
# From fixed tracial separation to hyperlinearity

A homomorphism into a tracial matrix ultraproduct initially supplies only a
fixed positive Hilbert--Schmidt separation.  This file gives an elementary
bridge from that fixed separation to the near-maximal separation used by
`IsHyperlinear`.

The key device is the unital padding `U ↦ U ⊕ 1` with an identity block of
the same dimension.  If `z` is the relative normalized trace of two original
unitaries, their padded relative trace is `(z + 1) / 2`.  Positive squared
Hilbert--Schmidt separation bounds `re z` away from `1`; the padding therefore
bounds `|(z + 1) / 2|` away from `1`, including when `z` is a scalar phase.
The conjugate-double amplification already formalized in
`HyperlinearNonScalar` then gives full hyperlinearity.
-/
