# Review of four distinct frontier advances

Date: 5 September 2026. Internal mathematical review only. None of the
proofs below is externally peer reviewed or formally verified.

The preceding goal turn made concrete progress by committing the
all-degree split-surjectivity proof. This round assigned three different
remaining problems to three agents; the root checked and strengthened
the existing LIX construction. The work excludes non-hyperlinear groups.

## LIX: trace, stable rank, and matrix stability

The root wrote [the complete strengthening](stw59-unique-trace-and-matrix-stability-2026-09-05.md).
The unitary-group agent independently checked its Stiefel connectivity,
local polar lift, numerical stable range, actual matrix naturality,
relative homotopy continuity, trace contraction, and trace pairing.
Both readers also inspected the original Nistor theorem used to compute
stable rank. No gap was found.

For every nonzero finite abelian group G, the constructed A_G has one
trace, stable rank two, K1 zero, and entire component group G. Every
M_m(A_G), m>=2, is K-stable. Thus both the full unital corner A_G and
its ambient M2(A_G) are simple, but their size-one stable maps behave
differently. No higher unstable-group computation for U(A_G) is claimed.

Both scoped native Cairn checks passed on 73 nodes (38 claims and
35 routes) before commit `0ba21d4d2`, which was pushed to main.

## LVIII: kernels supported by a varying small projection

The unitary-group agent wrote [the supported-kernel proof](stw58-small-projection-support-kernel-contraction-2026-09-05.md).
The root reviewed the complete proof and checked the cited stable-rank
extension and crossed-product bounds in Blackadar's text.

For connected finite CW X of dimension d and simple stable-rank-one B,
a stably null unitary supported by p contracts if d[p]<=[1-p]. In the
finite pure case, a uniform normalized quasitrace bound strictly below
1/(d+1) supplies this comparison. The projection can vary over X.

The review required explicit fullness of p in C(X,B), so stable nullness
could be transferred back through the corner K1 map. It checked the
skeletal stable-rank bound, actual partial-isometry matrix copies,
central weighting of quasitraces, the normalization of unbounded
quasitraces for strict comparison, and the based-sphere normalization.
The original Rieffel bibliography title was corrected. Arbitrary
localization into such a projection support is still unproved.

## LXI: a larger algebra of obstructed mixed unitaries

The free-product agent wrote [the enlarged Fock proof](stw61-circle-and-properly-infinite-coefficient-fock-obstruction-2026-09-05.md).
The root checked the placement of the sign unitary, all commutation
relations, the retained Toeplitz defect, and the exact norm distances.

The allowed algebra contains the circle unitary, a unital properly
infinite T2 coefficient copy, and the distinguished mixed self-adjoint
letter. Every unitary in this generated algebra has commutator norm
one with the conjugated distinguished projection. That projection
has distance exactly 1/2 from the allowed algebra.

The review required an explicit faithful T3 embedding into the original
T2 and use of the full free-product inclusion theorem. Prefix parsing
proves faithfulness. The constructed Fock representation need not
extend to the larger original algebra. Arbitrary full-free-product
unitaries remain outside the theorem.

Both scoped native checks passed on 77 nodes (40 claims and 37 routes)
with the LVIII and LXI additions before commit `36fc48297`, which was
pushed to main. A trailing blank line reported by the whitespace check
is removed in the following integration batch; no mathematics changed.

## LXXVI: realization with a closed compact stratum

The Cuntz-semigroup agent wrote [the mixed realization proof](stw99-lxxvi-closed-compact-stratum-realization-2026-09-05.md).
The root reviewed its actual neighborhood projection frames, strict
collar embeddings, continuous scalar weights, and all three global
comparison arguments.

For finite-dimensional compact metric X and simple separable stably
finite pure real-rank-zero D, a target positive class lifts through
first-factor Cu inclusion when its restriction to a closed Y is
compact and every fiber off Y is soft or zero. The projection bundle
need only extend to a neighborhood of Y.

The proof builds increasing source classes whose compact neighborhoods
shrink to Y. It proves the last reverse comparison by a relative
embedding of every target cutoff, rather than deducing equality from
fiber classes alone. The review also required the Y-empty case to be
proved by strict-relative cutoff comparison, without assuming that
pointwise softness automatically means global softness.

Arbitrary accumulating compact strata and the general first-factor
surjectivity problem remain unresolved.

## Validation scope and problem count

All native graph validation runs use the existing MSI environment at
`/projects/standard/hsiehph/sauer354/stw79-cairn-check-20260904/cu-all-base-scope-20260905/`,
running `check --changed` and `preview`. They validate the stated
dependency closure, not all concurrent repository work and not the
mathematical proofs themselves. Logs are `proof-batch-check.log` and
`proof-batch-preview.log` in that directory and are replaced by later
scoped runs.

After integrating the closed-stratum theorem, both commands passed on
the expanded closure of 79 nodes (41 claims and 38 routes). All four
new claims derived as established. The named-root statuses were
unchanged. All remote validation and PDF-rendering jobs completed;
the original Nistor pages used the existing MSI PDF dependency cache.

The named-problem count remains one internally reviewed full solution
manuscript, for LIX. LVIII, LXI, and LXXVI remain open. The new bounded
theorems strengthen the associated routes without changing those root
statuses or asserting publication priority.
