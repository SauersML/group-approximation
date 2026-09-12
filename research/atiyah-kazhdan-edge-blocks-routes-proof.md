---
rg: 2
id: atiyah-kazhdan-edge-blocks-routes-proof
kind: route
title: Property (T) is nonamenable and non-indicable, killing the flatness and Hughes-free hypotheses
target: atiyah-kazhdan-edge-blocks-both-permanence-routes
requires: []
---

Both failures are direct consequences of two standard properties of an infinite
property (T) group `C`.

**Nonamenability.** An infinite group with property (T) is nonamenable
(a Kazhdan group is amenable only if finite). Lück's dimension-flatness
`Tor^(C[C])_p(N(C), -) ` vanishes in von Neumann dimension for amenable `C`,
and this is the input to the Mayer--Vietoris / tree computation of the induced
`L^2`-dimensions for `A *_C B`. For nonamenable `C` the flat-dimension argument
is not available, so the computation that would force integer dimensions over
`G` from integer dimensions over the pieces does not run.

**Non-indicability.** Property (T) forces `H_1(C; Z) = C^ab` finite (the trivial
representation is isolated, so `C` has no nontrivial homomorphism to the
amenable group `Z`). Hence the finitely generated subgroup `C <= G` does not
surject onto `Z`, and `G` is not locally indicable. Jaikin-Zapirain's
construction of the Hughes-free division ring of fractions of `K[G]`, and the
resulting Strong Atiyah conclusion, require local indicability, so they do not
apply to `G`.

These are properties of the edge group alone; no feature of the vertices or of
the specific compressions is used. The statement is therefore about the
unavailability of the two frameworks, not about the truth value of Strong
Atiyah for `A *_C B`, which stays open.
