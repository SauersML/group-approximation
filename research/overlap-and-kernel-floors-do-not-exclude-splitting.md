---
rg: 2
id: overlap-and-kernel-floors-do-not-exclude-splitting
kind: claim
title: Face-overlap and kernel-cycle floors alone do not exclude a noncanonical ucp splitting
distinct_from:
  triangle-lifts-avoid-both-tree-anchor-faces: that proves every accurate lift in the actual extension stays away from two elementary anchors; this constructs a split triangle model whose exact section lives in precisely that noncanonical middle region.
  three-face-ucp-balancing-needs-macroscopic-tree-motion: that proves the kernel-cycle floor for every ucp map into the relator extension; this preserves the same floor in a larger split model and shows that satisfying it is compatible with exact splitting.
  fd-representation-packets-never-obstruct-ucp-sections: that gives packetwise sections for arbitrary quotients; this is one explicit global split extension retaining the named triangle faces, diagonal group-word lifts, and the nontrivial kernel holonomy.
---

**ESTABLISHED (triangle-respecting middle-region countermodel).**  Start with
the explicit triangle extension

```text
q_0:A_0=C^*(G_0)->>Q=C^*(Lambda)
```

and form

```text
A_split=A_0 direct_sum Q,
q_split:A_split->>Q,       q_split(a,x)=x.                 (OKF1)
```

The map

```text
s_split:Q->A_split,
s_split(x)=(epsilon(x)1_(A_0),x)                           (OKF2)
```

is a unital star-homomorphic section.  Hence its restriction to `S_Delta` is
an exact ucp local splitting.

Nevertheless the full triangle word geometry and kernel-cycle norm floor
remain visible.  Represent `G_0` diagonally by

```text
Delta(g)=(u_g,u_(q_0(g))) in U(A_split).                   (OKF3)
```

For the fixed reduced kernel word `n=a_1...a_L`, put

```text
w_j^split=Delta(a_j)=(w_j,v_j),
Delta(n)=(u_n,1).
```

Then

```text
||1-Delta(n)||=||1-u_n||=2,                                (OKF4)
```

and the same Stinespring/kernel-cycle proof gives, for every ucp
`Phi:S_Delta->A_split`,

```text
max_j||Phi(v_j)-w_j^split||>=2/L^2.                        (OKF5)
```

The exact section `(OKF2)` simply pays this floor in the first summand:

```text
s_split(v_j)-w_j^split=(1-w_j,0).                          (OKF6)
```

It also lies a fixed distance from the scalar-tree face because its second
summand is the identity map on every face.  Thus it occupies exactly the
noncanonical middle region left by the two-anchor theorem while splitting
perfectly.

**Sharp scope.**  This is not a counterexample to the actual Kac--Moody
lifting claim.  `A_split` is not RFD because it contains the non-RFD quotient
as a direct summand, and `ker(q_split)=A_0 direct_sum 0` is larger than the
native relator ideal.  That failure is the point: no theorem using only the
three finite face overlaps, scalar-tree transversality, and the kernel-cycle
Gram floor can decide the middle region.  A decisive argument must use an
additional global feature of the actual extension, such as RFD together with
quantitative control of the native relator ideal/support.  Reapplying the two
local floors cannot suffice.

Proof: `add-a-split-quotient-summand-and-keep-the-diagonal-kernel-word`.

DERIVATION
add-a-split-quotient-summand-and-keep-the-diagonal-kernel-word
