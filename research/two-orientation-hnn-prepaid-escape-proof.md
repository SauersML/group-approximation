---
rg: 2
id: two-orientation-hnn-prepaid-escape-proof
kind: route
title: Route each oriented coarse half into the sibling controlled-sign complement
target: two-orientation-hnn-packet-prepays-escape
requires:
  - controlled-pauli-corner-has-clifford-groupification
  - primitive-clifford-type-fixes-orientation-not-return
  - balanced-hnn-conditional-gap-forces-carrier-escape
  - finite-packet-flow-keeps-payload-orientation-balanced
---

Use the two four-dimensional extensions `S_+` and `S_-`.  Formula `(TOH2)`
is immediate from `J=-1` and `s=C,-C` on the two summands.  Schur form for a
packet-reducing payload carrier gives the rank ratios in `(TOH6)`.

On `S_+ direct-sum S_-`, choose `U_+` to send the two-dimensional space
`eS_+` into the three-dimensional space `f_+S_-`, complete its action on
`eS_-` so that `U_+(eV)=f_+V`, and extend unitarily on the complements.
Then `U_+Z_1U_+^*=s`.  Construct `U_-` in the same way with the signs
reversed.  The two letters have no mutual relation, so the choices coexist.

Tensor these balanced modules over all fresh packets and let each HNN letter
act only on its packet factor.  Joint primitive atoms have relative trace
`2^(-N)`.  The packet hull of a nonzero vector in the sibling spin type is
the whole sibling irreducible, giving exactly the factor-two release stated
in the claim.  Tensoring with a scalar structural BCS assignment preserves
all centralizer relations and can leave a forbidden assignment projection
equal to one.

