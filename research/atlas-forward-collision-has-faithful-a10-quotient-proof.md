---
rg: 2
id: atlas-forward-collision-has-faithful-a10-quotient-proof
kind: route
title: Verify the degree-ten A10 certificate by exact permutation arithmetic
target: atlas-forward-collision-has-faithful-a10-quotient
requires:
  - atlas-forward-collision-bass-serre-reduction
artifacts:
  - experiments/atlas_a4_forward_collision_a10_certificate.g
  - research/artifacts/atlas-a4-forward-collision-a10-certificate.json
---

Load the five permutations `(A4-A10-1)` in GAP 4.14.  The certificate script
evaluates all twelve relators of the presentation in
`atlas-forward-collision-bass-serre-reduction` and asserts that each is the
identity.  It then computes the five subgroup orders in `(A4-A10-2)`.
Comparison with the known orders `18,144,6,9,2` proves injectivity of every
vertex and edge map, because each restricted homomorphism is a surjection
from the correspondingly presented finite group to an image of full order.

The generated permutation group has order `1814400`, and `SignPerm` is one on
each generator.  It is therefore a subgroup of `A10` having the full order of
`A10`, hence equals `A10`.  No group identification database or probabilistic
recognition is used.

Finally restriction of `Reg(A10)` to a subgroup `H` is
`[A10:H] Reg(H)`.  The three indices are `100800,12600,302400`, and division
by the Bass--Serre multipliers `1120,140,3360` gives the common atlas
multiplicity `90`.  This proves the regular-carrier statement.
