---
rg: 2
id: atiyah-kazhdan-edge-blocks-both-permanence-routes
kind: claim
title: A property (T) edge group defeats both general amalgam-permanence routes for Strong Atiyah
distinct_from:
  atiyah-amalgam-unmixed-matrices-reduce-to-factors: that handles subgroup-supported matrices over any amalgam by induction; this explains why the two general frameworks for amalgam permanence of Strong Atiyah both fail exactly at a property (T) edge group, so the mixed matrices are not reachable by either.
  atiyah-passes-to-torsion-free-elementary-amenable-extensions: that is a positive permanence theorem for torsion-free elementary amenable quotients; this records that the edge-group analogue is unavailable for a Kazhdan edge because both proof frameworks need a hypothesis property (T) denies.
  algebraic-strong-atiyah-counterexample-exists: that seeks one torsion-free counterexample; this says the natural host, the double-HNN kernel amalgam over a Kazhdan edge, is exactly where no known permanence theorem decides Strong Atiyah.
---

**ESTABLISHED** (as a statement about the two known routes, not about the
conjecture). Let `G = A *_C B` with `C` an infinite property (T) group -- for
instance the kernel amalgams `P^(u_1) *_P P^(u_2)` over the Kazhdan subgroup `P`
of `fournier-facio-one-compressor-subgroup-reduces-to-gamma`. The two general
methods that establish Strong Atiyah permanence for amalgams both fail here, for
independent reasons:

1. **Amenable-edge dimension-flatness (Lück).** The Mayer--Vietoris computation
   of `L^2`-dimensions over the Bass--Serre tree closes only when `N(C)` is
   dimension-flat over `C[C]`, which holds under amenability of `C` (Følner
   sets). A property (T) group is nonamenable, so this flatness fails and the
   Mayer--Vietoris route gives no integrality.

2. **Locally indicable Hughes-free division ring (Jaikin-Zapirain).** For a
   locally indicable group `K[G]` has a Hughes-free division ring of fractions,
   and Strong Atiyah follows. But `C` is a finitely generated subgroup of `G`
   with finite abelianization (property (T)), so `C` does not surject onto `Z`;
   `G` is therefore not locally indicable, and the Hughes-free framework does
   not apply.

Neither route is available, which is the precise content of the remark in
`fournier-facio-one-compressor-subgroup-reduces-to-gamma` that "no elementary
permanence theorem covers those". Combined with
`atiyah-amalgam-unmixed-matrices-reduce-to-factors`, the open part of Strong
Atiyah for this host is exactly: matrices whose support mixes the two vertices
across the property (T) edge, where both standard proof frameworks are silent.

This is an obstruction to two proof strategies. It neither proves nor refutes
Strong Atiyah for the amalgam.

Proof: `atiyah-kazhdan-edge-blocks-routes-proof`.
