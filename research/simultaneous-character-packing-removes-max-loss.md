---
rg: 2
id: simultaneous-character-packing-removes-max-loss
kind: claim
title: Simultaneous orthogonal character packing removes the maximal-type loss
root: true
artifacts:
  - research/simultaneous-character-packing-removes-max-loss-proof.md
distinct_from:
  single-selected-atom-escape-compiler: that selects one maximal forbidden type and pays the factor M; this packs every forbidden type in one orthogonal family and removes that factor.
  finite-depth-adaptive-selected-atom-escape-tree: that grows a reducing carrier by repeatedly selecting one maximal atom; this is a one-step trace-capacity theorem and needs no reducing hull or iteration.
  index-two-reynolds-atoms-have-orthogonal-hnn-transports: that constructs separate equal-capacity destinations for individually named Reynolds atoms; this computes the sharp global capacity threshold when all transported forbidden atoms are mutually orthogonal.
---

Let `Gamma` contain a central involution `J`, put

```text
Q_-=(1-J)/2,
```

and let `e_1,...,e_M` be finite-subgroup character projections below `Q_-`.
Suppose canonical normalized-Hilbert--Schmidt microstates, after a fixed
finite-packet correction, satisfy

```text
sum_i tr(e_i)>=beta tr(Q_0)-o(1),
tr(Q_0)->a>0,
tr(Q_-)->h.                                              (SCP1)
```

Assume there are fixed group words `g_(i,r)`, `1<=r<=K`, such that the
projections

```text
p_(i,r)=g_(i,r) e_i g_(i,r)^(-1)                        (SCP2)
```

are pairwise orthogonal for all distinct pairs `(i,r)` and remain below
`Q_-`.  Then

```text
K beta a<=h.                                             (SCP3)
```

Consequently, if `K beta a>h`, the group has no canonical matrix
microstates and is nonhyperlinear.

For the Pauli half-sector initialization

```text
a=1/4,                 h=1/2,
```

the contradiction threshold is

```text
K>2/beta.                                                (SCP4)
```

This is sharper than packing only the conjugates of one maximal forbidden
type.  If orthogonality is known only within each fixed `i`, selecting a
maximal type loses the factor `M` and gives the weaker threshold

```text
K>2M/beta.                                               (SCP5)
```

Thus the decisive finite design problem is simultaneous packing of the
whole forbidden family, not a larger orbit for one payload chosen after the
microstate is known.
