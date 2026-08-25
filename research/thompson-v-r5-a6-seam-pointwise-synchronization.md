---
rg: 2
id: thompson-v-r5-a6-seam-pointwise-synchronization
kind: claim
title: R5 synchronizes adjacent Carmichael A5 charts across their A6 seam
distinct_from:
  thompson-v-r5-coherent-carmichael-family: that asks directly for one global unbounded Carmichael family; this asks for contextual three-generator charts with pointwise consistency on every adjacent overlap.
  thompson-v-r5-coherent-alternating-packet: that asks for all swap names and the full symmetric-group multiplication table; this asks only for adjacent A5 charts in the common-pivot Carmichael star.
  thompson-v-r5-uniform-common-pivot-centralizers: that false claim asks for bounded fillings of the individual escaping endpoint-centralizer loops; this permits one interacting R5 seam comparison and does not split it into separately filled centralizer corrections.
  a5-a4-overlap-has-two-seam-charges: that theorem shows why A4 restriction agreement alone is insufficient; this asks R5 to eliminate those two private seam directions quantitatively.
  bare-r5-a6-collision-does-not-synchronize-shared-labels: that exact five-dimensional countermodel shows that two local A5 packets plus the lone nonshared R5 collision do not control the shared contextual labels; this claim must additionally exploit a label-sensitive Bleak--Quick transport or split anchor coming from the fact that all occurrences are words in one approximate model.
---

In the Bleak--Quick presentation of Thompson `V`, put

```text
b=(01 10 11),                 B=U(b),
delta=def_R(U).
```

Prove constants `C,delta_0>0`, independent of matrix dimension and packet
size, such that whenever `delta<=delta_0` and `M>=3`, there are unitary
conjugates

```text
Y_i^T=W_i^T B (W_i^T)^*       (T in binom([M],3), i in T)
```

with

```text
||(Y_i^T)^3-I||_2 <= C delta,
||(Y_i^T Y_j^T)^2-I||_2 <= C delta              (i!=j in T),       (A6S1)
```

and, for adjacent charts,

```text
||Y_i^T-Y_i^(T')||_2 <= C delta
       whenever |T intersect T'|=2 and i in T intersect T'.       (A6S2)
```

The intended local geometry is that `T` supplies three moving leaves and the
two common pivots, hence an `A5` Carmichael chart.  Two adjacent triples have
union four, so together with the pivots they form the `A6` collision packet.
The R5 cell across the two nonshared leaves must remove both exact seam modes
identified by `a5-a4-overlap-has-two-seam-charges`, not merely show that the
two restrictions are isomorphic as `A4` representations.

This is deliberately a pointwise claim.  Average Johnson-graph energy does
not control every pair when the packet size is chosen after the matrix
dimension.  A proof also cannot fill the two endpoint centralizer loops
separately: `finite-mark-centralizer-commutator-area-is-proper` rules that out.
The required estimate must come from an interacting bounded R5/A6 seam or an
equivalent positive matrix inequality which retains both occurrences.

## Attempts

The direct common-frame attack splits an adjacent seam into two commuting
corrections in `C_V(b)`.  It dies because
`finite-mark-centralizer-commutator-area-is-proper` makes the filling areas of
those individual corrections diverge with their address distance.  Multiplying
the corrections around chart cycles does not repair this:
`collective-centralizer-cycles-are-free-gauge-identities` shows that the
resulting boundary freely telescopes and retains no matrix error.  The next
viable attack must therefore keep the two nonshared occurrences together in
one R5 collision channel and prove `(A6S2)` before separating endpoint gauges.

The bare collision channel is still insufficient.  In
`bare-r5-a6-collision-does-not-synchronize-shared-labels`, the standard
five-dimensional `A6` module gives two exact adjacent A5 charts and an exact
nonshared R5 relation, while the two common contextual labels are interchanged
and remain at squared normalized-HS distance `6/5`.  Thus the next attack
must retain at least one **label-sensitive** occurrence anchor across the
seam.  The concrete candidates in the Bleak--Quick presentation are R2,
`(1 01)^(1 00)=(00 01)`, and R3,
`(1 00)=(10 000)(11 001)`; R5 itself is only the disjoint-support commutator
`[(000 010),(10 110)]=1` and cannot distinguish the two shared labels.
