---
rg: 2
id: atlas-no-split-perfect-2-extension-of-a5-acts-on-f3-four-space
kind: claim
title: No nontrivial split perfect 2-extension of A5 acts faithfully on the four-dimensional F3 seam packet
artifacts:
  - experiments/atlas_a4_q1920_split_2byA5_gl4_classification.g
  - research/artifacts/atlas-a4-q1920-split-2byA5-gl4.json
distinct_from:
  atlas-q1920-smallest-mixed-solvable-kernel-is-impossible: that excludes an elementary abelian 2^9 action by weight spaces; this exhausts nonabelian 2-kernels as well.
---

Let `X` be the action group induced on a four-dimensional irreducible
`F3[A5]` chief factor by a quotient of the universal seam group.  If the
radical acting before this first odd layer is a 2-group `R`, then

```text
X = R semidirect A5
```

is perfect: the universal seam group is perfect, and every homomorphic image
is perfect.  Since `X <= GL4(3)`, the identity

```text
v_2(|GL4(3)|)=9,          v_2(|A5|)=2
```

forces `|R|<=2^7`.  Consequently every abstract possibility occurs in the
complete perfect-group lists at the eight orders `60*2^a`, `0<=a<=7`.

There are exactly nine groups in those lists whose Fitting subgroup is the
full 2-kernel, whose quotient is `A5`, and which contain an `A5` complement.
Exact modular representation calculation shows that each has one
four-dimensional irreducible representation.  For the trivial-kernel group
its image has order 60; for all eight nontrivial-kernel groups the image also
has order 60.  Thus every such representation kills `R`:

```text
R nontrivial  ==>  no faithful X -> GL4(3).                (Q1920-2A5-1)
```

This includes the split extraspecial candidate of order 1920.  The related
nonsplit perfect group of order 1920 does have a faithful four-dimensional
representation, but it has no `A5` complement and therefore cannot be an
action image of the fixed splitting `P=N semidirect A5`.

## Attempts

The elementary weight-space argument only handled an abelian 2-kernel;
`(Q1920-2A5-1)` closes all nonabelian 2-kernels allowed by `GL4(3)`.  It still
does not exclude a solvable action radical containing an odd chief factor
before the four-dimensional packet.  Such a radical is the exact remaining
escape from the solvable-kernel program.
