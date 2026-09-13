---
rg: 2
id: eta-cubed-lambda-mod-eight-bordism-proof
kind: route
title: The relative lambda number is the e-invariant mod 24, and a BSpin_8 null-bordism forces it to be divisible by 8
target: eta-cubed-survives-in-lambda-mod-eight-bordism
requires: []
artifacts:
  - research/artifacts/class-four-lambda-mod-eight-trapping-2026-09-13.md
---

Part 1, Proposition 1.1.

A framed 3-manifold L bounds a spin W. The framing gives a relative class
lambda(W, ∂W) in H^4(W, ∂W; Z) ≅ Z. Its value mod 24 does not depend on W:
two choices glue to a closed spin V with <lambda(V), [V]> = 3·sigma(V)/2, and
Rokhlin's theorem makes that divisible by 24. The Lie-framed SU(2)
represents nu and gives ±1, so this invariant is an isomorphism
pi_3^s -> Z/24. It takes eta^3 = 12 nu to 12.

If L bounds a BSpin_8-manifold W extending the framing structure, then the
nullhomotopy of lambda mod 8 extends over W rel ∂W. The obstruction to that
extension is lambda(W, ∂W) mod 8, so the invariant is 0 mod 8. But 12 is not
0 mod 8.

Standard inputs: eta^3 = 12 nu (Toda), Rokhlin's theorem, and the fact that
the Lie-framed S^3 represents nu.
