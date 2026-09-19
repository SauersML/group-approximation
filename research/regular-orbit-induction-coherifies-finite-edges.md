---
rg: 2
id: regular-orbit-induction-coherifies-finite-edges
kind: claim
title: Regular-orbit induction turns any finite orbit of edge maps into one equivariant edge
distinct_from:
  finite-symmetry-equivariant-edge-has-one-holonomy: that proves the one-holonomy consequence after an equivariant edge has been supplied; this constructs such an edge from finitely many incoherent directional copies.
  unstabilized-reset-pencils-have-no-s3-symmetry: that rules out coherence on one residual copy; this obtains coherence by a fixed regular-orbit stabilization.
  finite-packet-graph-atlases-have-a-regular-stationary-flow: that uses regular representations to show type tables alone cannot produce a gap; this is an equivariantization construction and still requires contextual success/failure words for payment.
---

Let a finite group `H` act transitively on a finite family of marked finite
edge monomorphisms

```text
phi_x:E_x -> F_x,             x in X.                    (ROI1)
```

No coherent action on the individual coefficient coordinates is assumed.
Fix `x_0` and form the componentwise products indexed by the regular `H` set:

```text
E_reg = centralProduct_(h in H,J) E_(h^(-1).x_0),
F_reg = centralProduct_(h in H,J) F_(h^(-1).x_0),
Phi_reg = centralProduct_h phi_(h^(-1).x_0).             (ROI2)
```

Let `H` act by left translation of the factors, using only the given
relabelings of the finite directional packets.  Then exactly

```text
Phi_reg(g.e)=g.Phi_reg(e),                               (ROI3)
```

so `Phi_reg` extends to an injective map of semidirect products

```text
E_reg semidirect H -> F_reg semidirect H.               (ROI4)
```

The construction multiplies every selected edge restriction by the same
fixed `|H|`-fold tensor factor.  Hence equality of restriction multiplicities
is preserved, as is every normalized type-vector mismatch.  The common
central sign remains one sign because `(ROI2)` is a central product over
`J`, not a product with independent marks.

If every factor is context-private and fixes a common logical BCS word, the
regular action also fixes that word.  Thus one may identify the logical
products of all private gauge decompositions without identifying their
individual shares.  Exact completeness is obtained by the finite gauge
orbit followed by countable amplification; finite-matrix soundness uses one
fixed enlarged packet, so its exactification constant remains independent of
ambient dimension.
