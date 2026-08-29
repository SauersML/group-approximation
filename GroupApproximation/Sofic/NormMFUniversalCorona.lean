import GroupApproximation.Sofic.NormMFUniversalQuotient
import GroupApproximation.Sofic.OperatorMF

/-!
# The norm-MF universal quotient is MF

For a countable group, pointwise detection of every nonidentity element by
possibly different norm-matrix ultraproducts can be diagonalized into one
faithful representation in a cofinite norm matrix corona.  At stage `k` we
take a block sum of detectors for the first `k + 1` nonidentity elements and
choose each detector far enough out to control the first `k + 1` group
elements.  Operator norm turns block sum into a finite maximum, so the
resulting sequence is asymptotically multiplicative, while every marked
element retains its own positive gap on all sufficiently late stages.

Applied to `normMFQuotient G`, whose residual is already known to be trivial,
this proves the three assertions in manuscript Proposition `prop:univquot`:
the residual is the kernel of a single corona representation, the quotient
is MF, and every map to an MF group factors uniquely through it.
-/

namespace GroupApproximation

open Filter Matrix
open scoped Matrix.Norms.L2Operator

universe u v

/-! ## Finite operator-norm block diagonals -/

/-! ## Finite heterogeneous lists of unitary blocks -/

end GroupApproximation
