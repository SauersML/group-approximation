---
rg: 2
id: iwahori-projective-sign-resolution-proof
kind: route
title: Compute the projection quadratic and exclude the mod-two sign on the edge
target: iwahori-edge-orientation-removes-projective-sign-branch
requires: []
---

For `Q=UPU^*`, expand

```text
tr((2P-1)(2Q-1))=4tr(PQ)-4tr(P)+1=1-2||[P,U]||_2^2.
```

The trace is real because it is the trace of a product of selfadjoint
operators.  Squaring its absolute value gives `(IER2)`.

If the projective energies tend to zero, then for every fixed generator
`c`, `Ad(pi_n(c))V_n` is asymptotically either `V_n` or `-V_n`.  Pass to a
subsequence on the finite generating set.  Bi-invariance and exact
multiplication show that the selected signs multiply on words; relators make
them descend to a character of `C`.  Edge commutation makes that character
trivial on `B`.

The abelianization of `SL_2(Z)` is cyclic of order twelve, so it has one
nontrivial character to `{+1,-1}`.  It is the sign after reduction to
`SL_2(F_2)=S_3`.  An index-three Iwahori subgroup is the inverse image of an
order-two point stabilizer, on which sign is nontrivial.  Therefore a sign
character trivial on `B` is trivial on `C`, and all generator commutators
tend to zero.

