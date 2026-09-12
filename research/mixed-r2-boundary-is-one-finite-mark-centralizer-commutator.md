---
rg: 2
id: mixed-r2-boundary-is-one-finite-mark-centralizer-commutator
kind: claim
title: The mixed R2 boundary is one finite-mark centralizer commutator
invalidates:
  - escaping-separate-endpoint-transport-closes-mixed-r2
  - canonical-depth-three-private-triangles-close-mixed-r2
distinct_from:
  finite-mark-centralizer-commutator-area-is-proper: that supplies the general Schreier-distance lower bound for a commutator with a fixed finite mark; this identifies the exact centralizer element hidden in the mixed R2 boundary and also records the fixed-local-diagram case where no escape occurs.
  mixed-r2-cell-couples-shared-s5-extension-multiplicities: that is an operator cancellation showing why the mixed cell would close the multiplicity seam; this is a free-word and van Kampen-area identity determining when such a cell can have bounded R1--R5 cost.
  depth-three-bq-arm-expansion-is-equivariant-under-label-flip: that is a fixed six-letter label-swap countermodel; this applies to a family of relative output corrections and distinguishes fixed local corrections from escaping ones.
---

Let `G=<X|R>` be the Bleak--Quick presentation, and suppose two contextual
R2 triangles have first-chart input `s_0`, first-chart transported arm `t_0`,
second-chart transported arm `t_1`, and common pivot `r`.  Use the convention
`x^y=y^(-1)xy` and put

```text
q=t_0^(-1)s_0t_0r^(-1),
w=t_1^(-1)s_0t_1r^(-1),
d=t_1t_0^(-1).                                                (MRB1)
```

After one use of the private R2 cell `q`, the mixed boundary is

```text
w  =_q  t_0^(-1)(d^(-1)s_0d s_0^(-1))t_0.                    (MRB2)
```

Consequently, if `q=1` and `w=1` in `G`, then `d in C_G(s_0)`.  If the
private R2 cell has area at most `A_0`, then

```text
|Area_R(w)-Area_R(d^(-1)s_0d s_0^(-1))| <= A_0.               (MRB3)
```

Now suppose `s_0=b^g`, where `b` is one fixed Bleak--Quick prefix
transposition.  Put

```text
dbar=d^(g^(-1)) in C_G(b).                                    (MRB4)
```

The theorem `finite-mark-centralizer-commutator-area-is-proper` gives
constants `A>0,B>=0`, independent of the occurrence, such that

```text
Area_R(w) >= A d_(<b>\G)(<b>,<b>dbar)-B-A_0.                  (MRB5)
```

Therefore a construction which forms the two transported endpoints
separately **and whose relative corrections `dbar` escape modulo `<b>`** cannot
prove the mixed-R2 occurrence claim with bounded R1--R5 cost.  This lower
bound permits arbitrary interacting ambient diagrams; combining more R1--R5
cells after the two endpoint gauges have been separated does not help.

This does **not** refute
`bleak-quick-adjacent-seam-retains-one-mixed-r2-cell`.  If the entire adjacent
seam is one conjugate by `g` of a fixed depth-three diagram, then

```text
t_0=a_0^g,       t_1=a_1^g,       dbar=a_1a_0^(-1),             (MRB6)
```

which lies in a fixed finite set of Schreier vertices.  In that case `(MRB5)`
has a bounded right-hand side, and finite-mark area properness supplies no
obstruction.  A surviving proof must retain the mixed boundary before the
two contextual output gauges are split, precisely as the open claim asks.

The canonical label-flipped depth-three pair does not supply that local
cancellation.  With

```text
s_0=(i p),       t_0=(i q),       t_1=(j q),       r=(p q),      (MRB7)
```

the swaps `t_1` and `s_0` are disjoint.  Hence its proposed mixed boundary is

```text
t_1s_0t_1r=s_0r=(i p)(p q),                                  (MRB8)
```

a three-cycle, not the identity.  Thus neither finite area nor a more clever
filling exists for the direct mixture of the two canonical private R2
triangles.  Any fixed-local proof must first alter which chart-one endpoint
is retained; it cannot simply splice the label-flipped words.
