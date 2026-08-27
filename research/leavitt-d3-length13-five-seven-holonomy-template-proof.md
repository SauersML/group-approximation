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
problem is only to solve the twelve displayed corner equations using the
thirteen cyclic coefficient slots.  There is **no** full-support or generating
packet condition: the equation may use any elements of the ambient Leavitt
group.  If its relative presentation kills the fixed nonidentity element
`h=[c,d]`, the coefficient map from that ambient group already fails to be
injective.  Equivalently, one may restrict afterward to the finitely generated
subgroup containing the coefficients and `h`.

For the sharper source choice `A^(-1)C=1`, let the seven alternating
coefficient units in the source corner be `A,B,C,D,E,F,G`, beginning and
ending in copy 2.  Exact free-product normal form gives four, and only four,
cancellation branches:

```text
I    B=D=F=1,       ACEG=1;
II   C=F=1, D=B^-1, AEG=B;
III  B=E=1, F=D^-1, ACG=1;
IV   C=E=1,         BDF=1, AG=B.
```

For the actual slots these are obtained from
`(A,B,C,D,E,F,G)=(g1,g2,g3,g4,g5,g6,g7)`.  Exact normal-form comparison in
the three-syllable target corner gives `g0=h`,
`g12=h g1^(-1)`.
If the unary pivot word `H` is additionally set equal to one, every one of
the four branches forces the common-carrier equation to compare `h_0` with
the reduced word `h_0 h_1`.  Thus the tempting `H=1` shortcut is impossible;
any solution must use genuine nontrivial pivot holonomy.
