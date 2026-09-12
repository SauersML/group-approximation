---
rg: 2
id: unconditional-bcs-decoder-ce-proof
kind: route
title: Apply the decoder to the trivial group homomorphism
target: unconditional-bcs-ultraproduct-decoder-forces-ce
requires: []
---

Choose any nonzero tracial matrix ultraproduct `M`.  Every group has the
homomorphism `rho_0(g)=1`.  By the unconditional hypothesis,
`Dec(rho_0):B->M` is a unital star-representation.  Composing it with the
normalized trace of `M` produces a tracial state on `B` realized in a
tracial matrix ultraproduct, hence a Connes-embeddable trace.

If the decoder lands in a nonzero corner `pMp`, compose with the normalized
corner trace; if it lands in `M_k(M)`, use the amplified normalized trace.
Thus neither standard convention avoids the conclusion.  A mark-relative
decoder avoids the argument precisely because the trivial homomorphism may
have zero marked corner and then supplies no unital representation of `B`.
