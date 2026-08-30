# Audit: prescribed-corner matrix-cone lifting no-go

Date: 2026-08-30

Claim: `stw22-bare-cone-projectivity-does-not-supply-ilr`.

## Checks

1. The normalized support trace is `1/(2m+1)` at zero and `2/(2m+1)`
   elsewhere, so the strict ILR bound `1/m` holds on the whole interval.

2. There is room for `m` orthogonal rank-two range projections because
   `2m<=2m+1`. The explicit partial-isometry construction therefore gives a
   single global ILR tuple.

3. The fibre cone map at zero is evaluation at the cone coordinate one
   followed by a matrix-corner inclusion. Its constant extension is an
   explicit unrestricted lift, so the example does not rely on an imported
   projectivity theorem.

4. A cone representation makes the diagonal support projections mutually
   orthogonal and Murray--von Neumann equivalent. Prescribing the first
   diagonal as `a(s)` for `s>0` therefore costs `2(m+1)` dimensions, one more
   than the available `2m+1`.

5. The obstruction is specifically relative. Ordinary cone lifting changes
   the positive corner away from the base fibre; ILR keeps the prescribed
   source but does not demand its support be orthogonal to the replication
   ranges.

## Consequence for XXII

Finite-dimensional cone projectivity alone cannot close the
positive-dimensional selection hinge. A useful cone reformulation would
use `M_m` and count `a^(1/2)` itself as the first of the `m` copies. Its
prescribed-corner local lifting property is exactly anchored ILR. This avoids
the extra source-orthogonality dimension cost of `M_(m+1)`, but remains a
relative lifting theorem: unrestricted projectivity still supplies no reason
for the lifted corner to equal `a` off the chosen fibre. That relative step
is substantive comparison and selection input rather than formal
projectivity.

## Independent audit

An independent adversarial audit verified the support traces, explicit
global ILR tuple, ordinary constant cone lift, diagonal-support rank
obstruction, and anchored-ILR reformulation. It requested only that the
matrix embedding be described as unital into its rank-`(m+1)` corner and
nonunital into `M_N`; the proof now states that distinction explicitly.
