---
rg: 2
id: two-sheet-projective-closure-forces-equivalent-carriers
kind: claim
title: Closed two-sheet projective dynamics forces equivalent carrier isotypes
distinct_from:
  pauli-swap-coherence-reduces-to-the-commutant-gate: that kills a discrete off-diagonal grading by perfectness; this classifies the full continuous matrix coefficient algebra
  presentation-defect-does-not-control-off-commutant-mass: that rules out projection without extra structure; this gives the exact extra structure needed for a projective rotation projection
  unbounded-commutant-coherence-is-the-original-gate: that starts after carrier/coefficient separation; this proves when such separation is possible for two sheets
---

Let `F` be a finite group and let `pi_0,pi_1:F->U(d)` be two carrier
representations. On `H=C^2 tensor C^d` put

```text
A_g=diag(pi_0(g),pi_1(g))
```

and let

```text
B=M_2(C) tensor I_d
```

be the scalar two-sheet coefficient algebra. The following are equivalent:

1. `Ad(A_g)(B)=B` for every `g in F`.
2. There is a character `chi:F->S^1` such that, after the chosen
   identification of the sheets,

```text
pi_1(g)=chi(g)pi_0(g)                    for every g.    (TPC1)
```

Thus a functorial projective rotation map on the two-sheet coefficient
algebra exists exactly for projectively equivalent carrier sheets.

For `F=GL_M(F_2)` with `M>=3`, the group is perfect, so `chi=1`.
Consequently the two sheets are equivalent and `B` lies in the carrier
commutant after one fixed change of sheet identification. Every closed
`SU(2)` rotation sector is therefore already covered by the commutant-
coherence theorems.

If `pi_0` and `pi_1` are inequivalent, conjugation by the carrier sends a
scalar off-diagonal Pauli matrix to an operator-valued intertwiner outside
`B`. Relator-smallness of the full tuple then does not define an
approximate homomorphism into `SO(3)`. The genuinely mixed survivor must
use precisely this carrier-assisted failure of coefficient closure.

DERIVATION
off-diagonal-matrix-unit-detects-projective-equivalence-proof
