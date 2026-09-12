---
rg: 2
id: jacobson-shift-representation-is-faithful
kind: claim
title: The shift representation of the Jacobson algebra over any cyclic coefficient ring is faithful
distinct_from:
  binary-jacobson-elementary-mark-is-finite-quotient-invisible: that is a group-level finite-quotient obstruction over the binary field; this is the ring-level monomial basis and faithfulness statement over the integers and every finite cyclic ring, with no group in it.
  finite-modulus-finitary-kernels-have-uniform-support-rank: that gives a uniform support-rank bound and a normal locally finite subgroup for the torsion-defect universal ring; this identifies the coefficient ring structure of the ambient algebra and extracts matrix coefficients as ring identities.
artifacts:
  - research/artifacts/fullness-corner-and-order-two-reduction-2026-09-08.md
---

**ESTABLISHED.**  For `C = Z` or `C = Z/mZ` put

```text
J_C = C<S,T | TS = 1>,      Q = 1 - ST,      Q_(ij) = S^i Q T^j.  (JSF1)
```

Let `S` and `T` act on `C^((N))` as the forward and backward shifts.
Then:

1. the representation is **faithful**, and the monomials `S^i T^j`
   (`i,j >= 0`) form a `C`-basis of `J_C`;
2. `Q_(ij) Q_(kl) = delta_(jk) Q_(il)`, so the `Q_(ij)` are the ordinary
   matrix units and their span is the ideal `F_C = M_fin(N,C)`;
3. the symbol sequence

```text
0 --> F_C --> J_C --> C[z,z^(-1)] --> 0                           (JSF2)
```
   is exact;
4. **coefficient extraction:** if `c in C` is the coefficient of `v_i` in
   `a v_j` for `a in J_C`, then

```text
Q T^i a S^j Q = c Q.                                              (JSF3)
```

`(JSF3)` is a ring identity, proved by comparing actions and then quoting
faithfulness; it is the tool that turns "an element acts as zero" into
divisibility statements about `C`.

DERIVATION
jacobson-shift-faithfulness-proof
