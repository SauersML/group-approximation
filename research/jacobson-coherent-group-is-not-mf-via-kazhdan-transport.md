---
rg: 2
id: jacobson-coherent-group-is-not-mf-via-kazhdan-transport
kind: claim
title: The faithful coherent Jacobson group is not MF, by Kazhdan transport through its own stable letter
distinct_from:
  jacobson-coherent-matrix-gap: that asks for gamma_triangle>0 with no property-T input; this proves the same sign using property (T) of EL_3(J), so it decides the alternative but does not discharge that node.
  jacobson-coherent-quotient-is-faithful-and-has-mf-dichotomy: that proves Rad_MF(Gamma_triangle) is 1 or L and leaves the choice open; this selects L.
  binary-jacobson-steinberg-head-root-is-mf-invisible: that kills x_13(Q) in EL_5(J), which needs the extra coordinate four for the commuting element; here the commuting element is manufactured inside Gamma_triangle from the stable letter, with no extra coordinate.
artifacts:
  - research/artifacts/rank-weighted-locally-finite-compression-2026-09-08.md
  - research/artifacts/jacobson-coherent-group-is-an-ascending-corner-extension-2026-09-08.md
---

ESTABLISHED (uses property (T)). Let `J=F_2<S,T | TS=1>`, `Q=1-ST`,
`M=EL_3(J)`, `phi(A)=Q I_3+S A T`, and

```text
Gamma_triangle = < M,t | t A t^(-1)=phi(A), A in M >.
```

Then every norm-corona representation of `Gamma_triangle` kills
`w=x_13(Q)`. Hence

```text
Rad_MF(Gamma_triangle)=L,   gamma_triangle>0,   Gamma_triangle is not MF.
```

**Consequences.**

1. **The coherent-gap lane is methodological.** `jacobson-coherent-matrix-gap`
   is true as a mathematical statement. What is still open is only a
   property-(T)-free proof of it, which is the same status as the goal.
2. **Gamma_triangle is the universal compression cell.** The rank-four
   cell `u` of `jacobson-compression-cell-is-a-commuting-lamplighter`
   satisfies `u A u^(-1)=phi(A)` on `H=EL_3(J)`. So `t -> u`, `M -> H`
   is a homomorphism `psi:Gamma_triangle -> EL_4(J)` with
   `psi(w)=x_13(Q)`. Pulling back MF representations gives
   `x_13(Q) in Rad_MF(EL_n(J))` for every `n>=4` from
   `w in Rad_MF(Gamma_triangle)`, with no further input. Therefore a
   (T)-free proof of `jacobson-coherent-matrix-gap` would give a (T)-free
   proof of `property-t-free-jacobson-head-collapse`. The coherent gap is
   a stronger sufficient condition, not a smaller piece.
3. **Permanence dichotomy.** At least one of these holds:
   - `EL_3(J)` is not MF, which is open (`jacobson-rank-three-parabolics-are-lef`);
   - an ascending HNN extension of an MF group by an injective
     endomorphism can fail to be MF.

   The hyperlinear analogue of the second alternative is false by
   `ascending-hnn-cannot-create-nonhyperlinearity`, so it is MF-specific.
   An MF-permanence theorem for ascending HNN extensions would therefore
   prove `EL_3(J)` not MF.

DERIVATION
jacobson-coherent-group-kazhdan-transport-proof
