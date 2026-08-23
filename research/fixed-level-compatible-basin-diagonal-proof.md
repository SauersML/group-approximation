---
rg: 2
id: fixed-level-compatible-basin-diagonal-proof
kind: route
title: Track the preconditioning error through the fixed-level stability radius
target: fixed-level-bs14-compatible-basin
requires:
  - bs14-full-commutant-finite-period-preconditioner
  - iwahori-square-root-presentation-is-bs14-plus-one-involution
  - bounded-period-iwahori-quotients-are-finite
---

An orbit of length `m<=K` has `S`-eigenvalues of order dividing `4^m-1`,
which proves `S^N_K=1`.  Its scalar monodromy is an `M`th root, so
`R^(mM)=1` on that packet; taking the least common multiple proves
`R^L_(K,M)=1`.  This gives `(FLB2)--(FLB4)`.

By `bounded-period-iwahori-quotients-are-finite`, the group in `(FLB4)` is
finite.  Finite-group normalized-HS stability therefore supplies the
fixed-level radius and flexible modulus used below; they are no longer
hypotheses.  Their dependence on `(K,M)` is uncontrolled.

Changing `R,S` by the preconditioner while leaving `x` fixed changes each
of the four bounded-length relative words by at most a universal word-
Lipschitz constant times `(BFP3)`, giving `(FLB5)`.  Under `(FLB6)`, choose
`j` and then take the original defect below `alpha_j`; the fixed-level
theorem applies at defect at most `2alpha_j`.  Sending `j` to infinity gives
the asserted flexible repair.

Conversely, pointwise positivity of `delta_j` imposes no comparison with
`alpha_j`.  The scalar schedules `(FLB7)` prove the logical nonimplication:
for every fixed `j` there is a stability neighborhood, while no
preconditioned tuple is guaranteed to enter it.  This is a quantifier fence,
not a counterexample to the actual fixed-level groups.
