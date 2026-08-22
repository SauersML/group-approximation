---
rg: 2
id: projective-transfer-reduces-to-complement-unitary-extension
kind: claim
title: Polar projective transfer reduces to one complement-unitary extension energy
distinct_from:
  leakage-small-polar-compressions-obey-projective-transfer: that zero-extends the corner witness and pays all boundary leakage; this allows a nontrivial complement unitary to synchronize the macroscopic boundary.
  canonical-exact-polar-models-have-flat-singular-loss: that shows singular modulus and relator data alone are insufficient; this identifies the genuinely joint witness-boundary quantity that remains.
  projective-trace-square-transfer-for-sl3-pair: that concerns arbitrary approximate arithmetic tuples; this is an exact-ambient polar-compression reduction using the established exact transfer theorem.
---

**ESTABLISHED CONDITIONAL REDUCTION.**  Let
`C=SL_3(Z)<A=SL_3(Z[1/2])`, let `pi:A->U(H)` be exact, let `P` have rank
`m>0` in `D=dim(H)`, and let

```text
T_s=Ppi(s)P,                 rho_s=polar(T_s).
```

Assume the target compression is uniformly nondegenerate:

```text
|T_h|>=sigma P                         for some sigma>0. (CUE1)
```

For `U in U(PH)`, define the scaled complement-extension energy

```text
J_C(U)= (D/m) inf_(Z in U((1-P)H))
          sum_(c in S_C) [1-|tr_H([U direct_sum Z,pi(c)])|^2]. (CUE2)
```

Then, for the dimension-independent exact projective-transfer constant `K`,

```text
1-|tr_PH([U,rho_h])|^2 <= (8K/sigma^2) J_C(U).           (CUE3)
```

Thus the surviving joint gate is precise: construct one complement unitary
`Z` whose ambient projective lattice-commutator energy is small on the scale
`m/D`.  Property `(T)` and arithmetic co-density then transfer automatically,
and polar Lipschitzness returns the conclusion to the retained corner.

This does not produce `Z` from the polar relators.  The flat-singular exact
calibrations show why modulus and relator data alone cannot do so.  In block
form, small `(CUE2)` simultaneously asks `Z` to intertwine the outgoing and
incoming leakage operators and to centralize the complement-complement
blocks.  That boundary synchronization is the remaining arithmetic content.

