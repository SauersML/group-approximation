import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-!
# The compact operators as a closed two-sided ideal of `B(H)`

The Calkin algebra `Q(H) = B(H) / K(H)` is what Enders--Shulman's proof of
Theorem 4.11 runs in, and `Analysis/ShulmanFillTheorem13` records that it is
not expressible against the pinned Mathlib.  This module builds the first of
the pieces it needs: the ideal.

`Mathlib/Analysis/CStarAlgebra/ContinuousLinearMap` gives
`CStarAlgebra (H →L[ℂ] H)` for a complex Hilbert space `H`, so `B(H)` is
available.  Mathlib's compact operators are a `Submodule`, not an ideal, so the
two-sidedness and the closedness are supplied here, in the shape
`Analysis/NormMatrixCorona` uses for the null ideal of the matrix corona: an
`Ideal` with an `Ideal.IsTwoSided` instance and a closedness theorem.

## What still stands between this and the Calkin algebra

Three things, and none of them is bookkeeping.

1. **The star.**  For `Q(H)` to be a `*`-algebra the ideal must be closed
   under the adjoint, that is `T` compact implies `Tᴴ` compact.  That is
   Schauder's theorem, and **it is not in Mathlib**: the string "Schauder"
   does not occur there in connection with compactness, `adjoint` does not
   occur in `Analysis/Normed/Operator/Compact`, and there is no lemma relating
   `IsCompactOperator` to `ContinuousLinearMap.adjoint`.  In Hilbert space it
   is cheaper than the Banach-space statement — `T` compact gives `T*T`
   compact, `|T| = (T*T)^{1/2}` compact by the continuous functional calculus,
   and `T* = |T|U*` for the polar decomposition — but it is still a theorem to
   prove, and it is recorded below as `CompactStarClosedStatement`.
2. **The quotient's ring and norm structure.**  Mathlib quotients normed
   *groups* by closed subgroups and stops there; there is no normed-ring
   quotient by a closed two-sided ideal.  Until this is done the C-star
   identity of step 3 cannot even be *written*, since `A ⧸ I` has no norm and
   no star to write it with.  `Analysis/NormMatrixCorona` builds
   its quotient's `SeminormedRing`, `NormedRing`, `CompleteSpace`, `Star`,
   `StarRing`, `NormedStarGroup`, `NormedAlgebra` and `StarModule` instances
   by hand, and the same has to be done here.
3. **The C-star identity.**  This is where the corona pattern does *not*
   transfer, and the difference is worth stating precisely.  The corona's
   `filterMatrixCoronaAlgebraCStarRing` is proved from the formula
   `‖π(a)‖ = limsup ‖aₙ‖`, which holds because that quotient is an `ℓ^∞`
   product modulo a null ideal; the identity then reduces to the C-star
   identity in each matrix coordinate.  `Q(H)` has no such formula — its norm
   is the essential norm `dist(T, K(H))` and there are no coordinates — so the
   identity has to come from the general theorem that a quotient of a C-star
   algebra by a closed two-sided ideal is again one, whose standard proof runs
   through an approximate unit of the ideal.  That is the residual
   `CalkinCStarIdentityStatement` below.

So the Calkin algebra is three theorems away, not one construction away, and
two of the three (Schauder, the quotient C-star identity) are results Mathlib
does not have.  The ideal itself, below, is unconditional.

Item 1 is now a theorem: `Analysis/CalkinSchauderProof.compactStarClosed`.  Items
2 and 3 turned out not to be owed at all — `Analysis/CStarIdealQuotient`,
`Analysis/CStarSeminormQuotient` and `Analysis/CStarIdealApproximateUnit` already
carry the quotient's ring, norm, star and C-star identity for every closed
star-stable two-sided ideal, and they are root-imported.
`Analysis/CalkinCStarAlgebra` assembles the three.

This module is in the root import list.  It was authored while builds were
suspended and has not been elaborated, so the first build after the suspension
is where its names are checked.
-/

namespace GroupApproximation
namespace CalkinAlgebra

variable (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-! ## The ideal -/

/-- **The compact operators on `H`, as an ideal of `B(H)`.**  Left
multiplication by a bounded operator is postcomposition, which preserves
compactness. -/
def compactIdeal : Ideal (H →L[ℂ] H) where
  carrier := {T | IsCompactOperator T}
  zero_mem' := isCompactOperator_zero
  add_mem' := fun ha hb ↦ ha.add hb
  smul_mem' := fun b _ ha ↦ ha.clm_comp b

@[simp] theorem mem_compactIdeal {T : H →L[ℂ] H} :
    T ∈ compactIdeal H ↔ IsCompactOperator T := Iff.rfl

/-- Right multiplication is precomposition, which preserves compactness too,
so the ideal is two-sided. -/
instance compactIdeal_isTwoSided : (compactIdeal H).IsTwoSided where
  mul_mem_of_left := fun b ha ↦ ha.comp_clm b

/-- **The ideal is closed in the operator norm.**  This is Mathlib's
`isClosed_setOf_isCompactOperator`, at the carrier of the ideal. -/
theorem isClosed_compactIdeal :
    IsClosed (compactIdeal H : Set (H →L[ℂ] H)) :=
  isClosed_setOf_isCompactOperator

/-! ## The two theorems the quotient still needs -/

/-- **Schauder's theorem**, in the form the Calkin algebra needs: the adjoint
of a compact operator is compact, so the ideal is `*`-closed and the quotient
inherits a star.  Written with `star` rather than `ContinuousLinearMap.adjoint`
because the star of `B(H)` *is* the adjoint, and the ideal's star-closure is
what consumes it.  Not in Mathlib; see this module's header for the cheap
Hilbert-space proof. -/
def CompactStarClosedStatement : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H), IsCompactOperator T → IsCompactOperator (star T)

/-! The C-star identity for the quotient is deliberately *not* stated here, and
the reason is the finding itself: `A ⧸ I` carries no norm and no star until
those instances are built, so `‖x‖ * ‖x‖ ≤ ‖star x * x‖` does not even
elaborate over it.  The identity can be named only after step 2 of the header
is done, which is why the order of work is forced — the ideal, then the
quotient's ring, norm and star instances, and only then the C-star identity as
the last residual. -/

end CalkinAlgebra
end GroupApproximation
