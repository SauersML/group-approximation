import GroupApproximation.Sofic.NormMFResidualDetector

/-!
# The universal quotient detected by norm-matrix ultraproducts

The operator-norm MF residual is the common kernel, element by element, of
all homomorphisms from a group to operator-norm matrix ultraproducts.  This
file packages the corresponding universal quotient.

Every homomorphism to an operator-norm matrix ultraproduct factors uniquely
through `normMFQuotient G`.  More generally, the same is true for every
target whose norm-MF residual is trivial.  The quotient itself has trivial
norm-MF residual: every one of its nonidentity elements is detected by some
operator-norm matrix ultraproduct representation.  Consequently it is the
largest quotient of `G` with this pointwise detection property.

This file alone does **not** assert `IsWeakMF (normMFQuotient G)`: passing
from pointwise detection, potentially using a different ultraproduct for
every nonidentity element, to one simultaneous matrix model requires a
diagonal block-amplification construction.  That construction, and the
resulting standard cofinite-corona MF theorem, are supplied downstream in
`NormMFUniversalCorona`; no such result is assumed in the proofs here.
-/

namespace GroupApproximation

universe u v

/-! ## Definition and the canonical map -/

/-! ## Universal factorization into matrix ultraproducts -/

/-! ## Pointwise detection and triviality of the quotient residual -/

/-! ## Universal factorization into every residually detected group -/

/-! ## Largest residually detected quotient -/

end GroupApproximation
