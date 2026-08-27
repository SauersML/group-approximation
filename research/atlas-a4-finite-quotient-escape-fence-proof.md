---
rg: 2
id: atlas-a4-finite-quotient-escape-fence-proof
kind: route
title: Use A8 simplicity, one packet involution, and the regular representation of a finite image
target: atlas-a4-finite-quotient-escape-fence
requires:
  - atlas-charts-overlap-trivially
  - atlas-shortest-a4-triangle-packet
  - atlas-a4-packet-letters-generate-both-a8-charts
  - atlas-word-19243-is-kernel-relation
  - atlas-a4-19243-classical-collapse
  - atlas-a8-minimal-four-transvection-cycle
  - universal-leavitt-el4-nonsofic
---

Write `i_1,i_2:A8 -> Gamma_A4` for the chart maps.  The canonical atlas map

```text
A8*A8 ->> L_(F2)(1,2)^x
```

kills every defining relator of `Gamma_A4`: the packet words are selected
from the exact Leavitt kernel and collision `19243` is independently
kernel-checked.  It therefore factors through a surjection from `Gamma_A4`.
The target is infinite and nonsofic with property `(T)`.  Since amenable
groups and their quotients are amenable, while every amenable group is
sofic, `Gamma_A4` is infinite and nonamenable.

Now let `phi:Gamma_A4 -> F` have finite image.  Simplicity of `A8` says that
each restriction `phi o i_j` is either trivial or injective.  Suppose the
first is trivial.  The packet contains a relation

```text
(b_2 a_1)^3=1,       ord(b_2)=2, ord(a_1)=3.
```

After killing the first chart this reads `b_2^3=1`; together with `b_2^2=1`
it gives `b_2=1`.  Thus the kernel of the second chart restriction contains
a nonidentity involution, and simplicity kills the entire second chart.
The packet has the factor-reversed orientation as well (equivalently, its
same ten-letter alphabet contains order-two letters on both factors), so the
same argument works with the charts exchanged.  Since the two charts
generate `Gamma_A4`, `phi` is trivial.  This proves the trivial/injective
dichotomy.

Assume next that `phi` is nontrivial and replace `F` by its image.  Both chart
images are copies of `A8`.  In the left regular representation of `F`, the
restriction to either chart is `[F:A8]` copies of `Reg(A8)`, and every packet
word and `q_19243` is exactly one.

At least one of the four cross elements

```text
phi(i_2(t)i_1(t)^-1),   t in {t01,t12,t23,t30},
```

is nonidentity.  Otherwise the two chart maps agree on the four
transvections; those transvections generate `A8`, so the two maps agree
everywhere.  This is a classical automorphism alignment satisfying both the
packet and collision, excluded by the exhaustive inner/outer alignment
audit.

The normalized trace of a nonidentity element in `Reg(F)` is zero.  Hence at
least one root deficit `x_t=sqrt(1-Re tau(phi(i_2(t)i_1(t)^-1)))` equals one.
If it is `x_12`, the ellipse is at least `x_12^2=1`; if it is one of the other
three roots, then `S=2x_01+2x_23+4x_30 >= 2`, so the ellipse is at least four.
This proves `(A4-FQ-ESCAPE)` and all stated consequences.
