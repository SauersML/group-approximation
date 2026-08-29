import GroupApproximation.Sofic.NormUltraproductSequentialExtraction

/-!
# Operator-norm MF groups and the cofinite norm-matrix corona

This file formalizes the group property called MF by
Carrión--Dadarlat--Eckhardt: a group embeds in the unitary quotient of a
sequence of finite complex matrix algebras by operator-norm-null sequences.

The quotient below is built directly from sequences of unitary matrices.  Its
null subgroup uses the cofinite filter, so it is the unitary-sequence model of
the usual `ℓ∞/c₀` norm matrix corona, rather than an ultrafilter quotient.
`Analysis.NormMatrixCoronaUnitary` constructs the genuine complex C-star
quotient, proves by coordinatewise polar correction that every quotient
unitary has a unitary-sequence lift, and bundles the canonical multiplicative
equivalence.  `Sofic.CDEOperatorMF` states the literal CDE predicate and proves
its equivalence with `IsOperatorMF` below.

The extraction theorem is deliberately direct.  If a marked element survives
in a cofinite corona, a choice of unitary lifts is asymptotically
multiplicative, while nontriviality means that the marked distance is bounded
below frequently.  Intersecting each eventual finite multiplication test with
that frequent separation set produces a sequential marked almost
representation.  Thus the analytic kill theorem can obstruct the standard MF
property without appealing to an informal equivalence with `IsWeakMF`.
-/

namespace GroupApproximation

open Filter Matrix
open scoped Matrix.Norms.L2Operator

universe u

/-! ## The cofinite norm-matrix corona -/

/-! ## A surviving mark yields a sequential marked model -/

end GroupApproximation
