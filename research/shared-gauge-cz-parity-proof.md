---
rg: 2
id: shared-gauge-cz-parity-proof
kind: route
title: Track stable-letter parity simultaneously in the outer quotient and multiplicity factor
target: shared-gauge-cz-cancellation-needs-an-identity-outer-anchor
requires: []
---

Equation `(SGC5)` is unitary telescoping:

```text
||TA-C tensor I||_2
 <=||T-C tensor V||_2+||(C tensor V)(A-I tensor V)||_2
 <=eta_T+eta_A.                                         (SGP1)
```

Substitute `TA` for the literal `R_f` in `(UBL7)` and apply the triangle
inequality to obtain `(SGC7)`.

For the obstruction, every packet letter has trivial image in `Out(P)`,
while each dressed occurrence `h_iuk_i` has image `[alpha]`.  The same
occurrence contributes one factor `V` on multiplicity.  Multiplying a word
therefore proves `(SGC9)` by induction on word length.  Inner automorphisms
of an extraspecial Pauli group act trivially on `P/Z(P)`, while `alpha`
acts nontrivially there, so the two parity classes cannot coincide.

Finally, for the balanced involution `(SGC10)`,

```text
||V-I||_2^2=2.                                          (SGP2)
```

Tensoring by a unitary label operator preserves normalized HS norm.  This
gives the exact odd-parity distance floor; the outer-quotient calculation
gives the even-parity failure.

