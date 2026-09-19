---
rg: 2
id: priority-decoder-lipschitz-under-selector-gate-alignment
kind: claim
title: Priority decoding is dimension-free Lipschitz under joint selector and gate alignment
distinct_from:
  odd-selector-priority-decoding: that constructs the priority partition and proves lossless within-context decoding; this compares two independently constructed contexts quantitatively.
  priority-decoded-contexts-are-not-glued-by-raw-gate-equality: that shows gate alignment without selector alignment is insufficient; this proves the matching positive estimate when both energies are present.
  zpc-context-mismatch-transducer: that must construct LCS checks realizing the hypotheses for the verifier's differently labelled local contexts; this is the analytic gluing estimate after such matched labels exist.
---

Let `(M,tau)` be a finite tracial von Neumann algebra.  For two contexts take
commuting selector involutions

```text
Z_1,...,Z_m,       T_1,...,T_m
```

(commutation is required within each displayed family, not between the two
families), and gate involutions `G_a,H_a`.  Assume `G_a` commutes with all
`Z_b` and `H_a` commutes with all `T_b`.  Form the priority projections

```text
P_a=(1-Z_a)/2,       W=product_a Z_a,       E=(1-W)/2,
Q_a=E P_a product_(b<a)(1-P_b),
```

and analogously `R_a,F` from the `T` family.  Complete the two odd-corner
decoders by the identity on their even corners:

```text
Uhat=(1-E)+sum_a Q_a G_a,
Vhat=(1-F)+sum_a R_a H_a.
```

Then

```text
||Uhat-Vhat||_2^2
 <= (2m+1) [ sum_a ||G_a-H_a||_2^2
             +(m^2+m/4) sum_a ||Z_a-T_a||_2^2 ].          (PAL)
```

The constant depends only on the finite number of branch labels, never on
matrix dimension.  Thus a context transducer does not need a new analytic
Poincare theorem after it exposes matched labels: squared selector-alignment
and raw-gate-alignment energies already control the completed decoded
mismatch.  The unresolved compiler problem is algebraic and combinatorial:
construct those matched selector labels from the overlapping local readable
contexts while preserving the exact ZPC model.
