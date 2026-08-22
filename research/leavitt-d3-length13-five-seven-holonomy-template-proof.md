---
rg: 2
id: leavitt-d3-length13-five-seven-holonomy-template-proof
kind: route
title: Absorb the extra target pair without disturbing the common carrier arcs
target: leavitt-d3-length13-five-seven-holonomy-template
requires:
  - leavitt-d3-length11-five-five-holonomy-template
  - leavitt-minimal-cycle-is-hnn-holonomy
---

The exponent-three length-thirteen profiles with a unary pivot are

```text
(1,1,11): 13,        (1,3,9): 130,        (1,5,7): 260.
```

A representative of the last profile has signs

```text
(-,-,+,-,+,-,+,+,-,+,+,+,+)
```

and, after cyclic rotation, residual stable-sign words

```text
sigma5=(-,+,-,+,+),
sigma7=(-,+,-,+,-,+,+).
```

For a signed corner list `(epsilon_i,C_i)`, pivot substitution contributes
the ordered product `prod H^(-epsilon_i) C_i`.  The five-corner calculation
from the length-eleven template gives

```text
H H^(-1) * H^(-1) H X * H H^(-1) A
* H^(-1) H Y * H^(-1) H B = X A Y B.
```

For the seven-corner list in the claim, the first four factors reduce to
`X C Y`.  The remaining three factors are

```text
H H^(-1) * H^(-1) H * H^(-1) H D = D.
```

Thus the two whole residual relators are precisely `XAYB` and `XCYD`, with
the same carrier words and orientations.  Tietze elimination gives the
displayed HNN holonomy.  The extra signed pair is important: it supplies two
additional compound-corner degrees of freedom on the target side while
leaving the desired quotient unchanged.

This is an abstract signed-corner realization.  The remaining coefficient
problem is to solve the twelve displayed corner equations using the thirteen
cyclic coefficient slots while retaining a generating packet.
