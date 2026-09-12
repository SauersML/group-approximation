---
rg: 2
id: anchored-pauli-payload-direct-product-proof
kind: route
title: Generate every Pauli from actor translates of the two anchors and identify the universal product
target: anchored-pauli-extension-splits-off-its-payload
requires: []
---

The pairing in `(APS1)` shows directly that `(APS2)` is a group action by
automorphisms.  Inside the presentation of `G`, each `t_i` commutes with
every word in the actor generators, and hence with every `q in Q`.
Consequently it commutes with both

```text
q x_1 q^(-1)=(beta(q)e_1,0,0),
q z_1 q^(-1)=(0,e_1^* beta(q)^(-1),0).
```

Surjectivity of `beta` and transitivity of `GL_n(2)` on nonzero vectors
and nonzero covectors give all translations `(v,0,0)` and all modulations
`(0,phi,0)`.  These generate `P_n`, including its central sign
`j=(0,0,1)=[x_1,z_1]`.  Hence every payload generator commutes with the
entire base `P_n semidirect Q`.

The defining generators therefore induce a surjective homomorphism
`(P_n semidirect Q) times L -> G`.  Conversely all the defining relations
of `G` hold in that direct product, giving a homomorphism in the other
direction.  Their composites fix every generator.  This proves `(APS4)`
and, in particular, proves that neither the base nor the payload has been
collapsed by the cross-relations.

There is an explicit embedding

```text
(P_n semidirect Q) times L
 -> (P_n semidirect GL_n(2)) times Q times L,
(p,q,l) |-> ((p,beta(q)),q,l).                            (APS6)
```

It is a homomorphism by the semidirect-product multiplication law and is
injective by inspection of its three coordinates.  The first target factor
is finite.  Therefore if `Q,L` are residually finite, finite quotients of
the target separate every nonidentity element of `G`.  The converse follows
because `Q` and `L` embed in `G`.

For hyperlinearity, take canonical finite-window unitary microstates for
`Q` and `L`, and the exact regular representation of the finite first
factor in `(APS6)`.  Their tensor products have vanishing multiplication
defect and canonical trace: the trace of a tensor is the product of the
traces, so every nonidentity target element has trace tending to zero.
For example, the defect of a product tensor is bounded by the sum of the
two input defects, by adding and subtracting the intermediate tensor and
using unitary invariance of normalized HS norm.  Restrict these microstates
to the embedded finite windows of `G`.  This proves the forward construction
in `(APS5)`; restriction to the embedded copies of `Q` and `L` proves the
converse.

For completeness, the free-group special case needs no approximation
theorem.  Given a nonempty reduced word of length `m` in a free group,
draw its labelled path on distinct vertices `0,...,m`.  Each free generator
specifies a partial injective permutation along its labelled edges; inverse
letters specify reversed edges.  Reducedness prevents conflicting incoming
or outgoing prescriptions at an intermediate vertex.  Complete each partial
permutation on the finite vertex set.  The resulting permutation action
sends the start of the word path to its different endpoint, and separates
the word in a finite quotient.  Products of these quotients separate every
finite collection of nonidentity words.

Finally, for a finite quotient separating a prescribed word window, its
left regular permutation matrices satisfy every group relator exactly and
have normalized trace zero on the separated nonidentity words.  They are
the asserted exact finite-quotient canonical microstates.  In particular
every nonidentity mark in such a window has squared HS distance exactly
`2` from the identity at zero relator energy.  A separated positive-energy
floor for this fixed-frame group would contradict these explicit models.
