---
rg: 2
id: atlas-augmented-thirteen-vf-fillings
kind: claim
title: The augmented Atlas quotient is thirteen fillings of one virtually free group
distinct_from:
  atlas-forward-collision-bass-serre-reduction: that absorbs one minimal forward carrier and leaves collision as one relator; this absorbs the complete twelve-edge packet and q14 and counts the unavoidable cycle fillings.
  atlas-a4-context-network-simultaneous-hs-exactification: that uses thirty context occurrences for analytic simultaneous rounding; this uses the twelve distinct packet relations and identifies the exact abstract quotient.
  atlas-augmented-relations-have-unbounded-chart-width: that rules out bounded alternating width using the Leavitt image; this locates why standard residual-finiteness theorems do not decide the quotient.
---

Let `A` and `B` be the two marked copies of `A8`.  For each of the twelve
distinct packet pairs, attach a bridge vertex `L_e ~= A4` to `A` and `B` by
its `C3` and `C2` subgroups, with orientations determined by that pair.  Add
one bridge vertex `L_14 ~= V4`, whose two `C2` edge groups map to the two
marked copies of `t23`.  Denote the resulting connected finite graph of
finite groups by `G` and put

```text
Pi=pi_1(G).                                             (AVF1)
```

The graph has fifteen vertices and twenty-six edges, hence first Betti number

```text
b_1(G)=26-15+1=12.                                     (AVF2)
```

Consequently `Pi` is virtually free, residually finite, and sofic.  For any
maximal tree, let `s_1,...,s_12` be its stable letters.  The exact augmented
Atlas quotient is

```text
Gamma_+=(A8*A8)/<<packet,q_19243,q_14>>
       ~=Pi/<<s_1,...,s_12,q_19243>>.                  (AVF3)
```

Thus the standard graph-of-finite-groups residual-finiteness theorem applies
to `Pi`, not to `Gamma_+`.  Nor is `Gamma_+` a one-relator quotient of the
virtually free carrier: twelve independent graph-cycle stable letters are
filled before collision is imposed.  In the minimal collision subcarrier the
remaining collision word is already cyclically reduced of relative length
six and fails strict relative `C'(1/6)`; no applicable torsion-quotient or
small-cancellation residual-finiteness theorem is thereby obtained.

The canonical binary-Leavitt image proves that the two chart vertex groups
still embed after all thirteen fillings, but it is a linear representation
over a noncommutative, non-directly-finite coefficient ring.  It therefore
does not invoke Malcev residual finiteness or provide a finite quotient.

Accordingly graph-of-finite-groups, ordinary one-relator, and linear-group
residual-finiteness tools stop at the same explicit subgroup: the normal
closure of the twelve cycle stable letters together with the hyperbolic
collision word in `(AVF3)`.  Proving residual finiteness or soficity of that
specific multiple filling remains open; no order-by-order finite-simple
sieve is implicit in this reduction.

The explicit maximal-tree elimination and dependency calculation are given
by `atlas-thirteen-vf-fillings-are-tietze-irredundant`: all twelve cycle
fillings become genuine packet compatibility relators, and collision remains
an independent thirteenth filling.
