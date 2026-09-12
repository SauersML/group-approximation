---
rg: 2
id: s4-nand-cycle-holonomy-is-one-s2-bit
kind: claim
title: The first S4 NAND cycle holonomy is one plus-sheet swap bit
distinct_from:
  s4-standard-corner-realizes-shared-nand-chord: that constructs one incidence star with a common chord inside one S4 corner; this computes the obstruction when separate S4 NAND charts are glued around a cycle through shared C2 marginals.
  coherent-balanced-context-permutations-would-give-a-ce-trace: that gives the global no-CE obstruction for arbitrary balanced coordinate packets; this identifies the complete first-cycle gauge group for the minimal three-dimensional NAND packet.
  first-cycle-signed-hecke-chord: that asks for an escaped algebraic closure in the general packet; this computes its rank-one finite-packet shadow as an explicit S2 holonomy equation.
---

Use at every NAND context the three-dimensional standard `S_4` packet, with
the two variables represented by disjoint transpositions.  Along an
incidence identifying one variable, the shared subgroup is
`C_2=<s>`.  The selected standard type restricts as

```text
rho|_(C_2)=2*1 direct_sum sgn.                          (NSH1)
```

The `sgn` sheet is one-dimensional and therefore has a unique rank-one
matching.  The `+` fiber has two rank-one sheets.  The NAND context
distinguishes them: one is the joint atom `(+,+)` and the other is
`(+,-)`, while the `-` fiber is the atom `(-,+)` and `(-,-)` is absent.

Consequently every rank-one coordinate/character Hecke matching across a
shared incidence has exactly one residual gauge

```text
pi_e in S_2,                                             (NSH2)
```

recording whether it preserves or swaps the two `+` sheets.  For a connected
network, gauge all vertex sheet labels along a spanning tree.  On the first
non-tree chord, the complete holonomy is

```text
h_C=product_(e in C) pi_e in S_2.                       (NSH3)
```

The local NAND atom labels extend coherently around that cycle if and only if

```text
h_C=1.                                                   (NSH4)
```

If `h_C` is the transposition, the returned `(+,-)` rank-one projection is
the orthogonal `(+,+)` projection.  Since these atoms give opposite values
to the other NAND variable, no endpoint gauge which preserves both the
shared marginal and the already-labelled context partition can repair the
swap.

Both edge choices in `(NSH2)` can be realized by exact finite-character
piece transports; thus no rank or integrality obstruction precedes
`(NSH4)`.  A graph of such finite charts is still virtually free, so solving
all its `S_2` cycle equations only gives a finite/CE corner atlas.  To use the
fixed no-CE BCS, the global compiler must promote at least one forced
nontrivial bit to a block-escaping algebraic holonomy rather than merely add
more finite S4 charts.

For unrestricted (not rank-one-coordinate) endpoint regauges the same
statement becomes: the holonomy lies in `U(2)` on the plus multiplicity
space and must stabilize the distinguished NAND atom line.  Equation
`(NSH4)` is the exact discrete Hecke specialization.

