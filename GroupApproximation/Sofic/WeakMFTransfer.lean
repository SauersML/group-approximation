import GroupApproximation.Sofic.WeakMFUltraproduct
import GroupApproximation.Sofic.LEFSofic

/-!
# Weak-MF transfer along group embeddings

Operator-norm matrix approximation is inherited by subgroups.  This elementary
fact is the last purely local step in the weak-MF amalgamation argument: once
an analytic construction embeds a group into an MF unitary group, the source
itself is weak-MF.

The proof below works directly with finite `NormModel`s.  It does not use an
ultraproduct, a trace, or any permanence theorem for C*-algebras.
-/

namespace GroupApproximation

open Matrix
open scoped Matrix.Norms.L2Operator

universe u v

/-! ## Exact finite models -/

end GroupApproximation
