---
rg: 2
id: final-rope-canonical-tensor-conjugator-is-not-faithful-proof
kind: route
title: Retract the outer edge subgroup and evaluate its canonical tensor conjugator
target: final-rope-canonical-tensor-conjugator-is-not-faithful
requires: []
---

Set the inner stable letter `v` equal to `1`.  The central HNN relations
remain valid, so this defines a retraction `r:Gamma->K`.  Both
`i(F)` and `v i(F)v^-1`, the generators of `S`, map into `i(F)`;
hence `r(S)<=i(F)`.

The element `k=((a,1),1)` is not in `i(F)`: comparison of the graph
factor's first coordinate would force the preimage `f` to equal `1`,
while comparison of the `K_0` first coordinate would then force
`a=1`.  Since `r(k)=k`, it follows that `k notin S`.

Therefore `(k,1)` is outside the source edge subgroup
`{(s,1):s in S}`, and Britton's lemma makes `[u,(k,1)]` nontrivial.
The graph-witness maps used for tensor synchronization kill the whole
`K_0` factor, so `lambda_n(k)=1`.  In the product model the image of
`(k,1)` acts only on the first factor, while `U_n=1 x W_n` acts only
on the second.  They commute exactly, and the commutator word is the
identity for every `n`.

No stronger conclusion follows: another edge intertwiner may mix the two
factors and need not commute with `pi_n(k)`.
