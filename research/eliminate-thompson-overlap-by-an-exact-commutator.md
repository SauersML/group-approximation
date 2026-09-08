---
rg: 2
id: eliminate-thompson-overlap-by-an-exact-commutator
kind: route
title: Express the overlap row as a commutator with the first Leavitt relation
target: leavitt-eight-word-packet-is-quantitatively-equivalent
requires:
  - leavitt-has-an-explicit-finite-c-killing-certificate
artifacts:
  - research/artifacts/leavitt-eight-word-exact-reduction-2026-09-08.md
---

Put `J=j`, `K=JC`, `R=K^2=r_*`, and `D=C^(-1)JC`. Because
`C^3=I`, one has `J=KC^(-1)`, `D=C^(-1)K`, and `JD=KCK`.
The overlap relator is consequently

```text
rho_4=(JD)^(-1)D(JD)J^(-1)
     =K^(-1)C^(-1)K^(-1)C^(-1) R C K C K^(-1).
```

Let `L=K^(-1)C^(-1)K^(-1)C^(-1)` and `M=CKCK^(-1)`.
Cancellation gives `LM=K^(-2)=R^(-1)`, so

```text
rho_4=L R L^(-1)R^(-1)=[L,R].
```

Unitary invariance and the triangle inequality give
`||rho_4-I||<=2||r_*-I||`. Also the compiler definition
`j=a C d C^(-1)a^(-1)` gives
`j^2=(aC)d^2(aC)^(-1)`, hence equality of these two defects.
All other rows are identical in the two packets, proving the factor-two
maximum-defect comparison and the squared-energy comparison.

The same identities prove equality of normal closures in `P`. Native
kernel membership and exact finite-dimensional cycle killing follow
from the required nine-word theorem. The artifact records the complete
eight-row specification and verifies its lengths.
