---
rg: 2
id: isolated-regular-a2-hexagon-has-free-external-holonomy
kind: claim
title: One regular A2 hexagon admits every external multiplicity holonomy
distinct_from:
  adjacent-a2-chambers-share-only-commuting-wall: that constructs independent exact regular packet algebras across one wall; this starts with a coherent six-chamber packet and shows that the compatibility intertwiners themselves retain a completely free amplified gauge.
  six-chamber-a2-holonomy-closes-fixed-clock-sector: that computes the holonomy of the literal Weyl words inside one fixed Chevalley packet; this concerns arbitrary edge compatibility intertwiners, which are not authenticated as those native words.
  finite-packet-graph-atlases-have-a-regular-stationary-flow: that solves all vertex and edge multiplicity equations; this exhibits the remaining full unitary freedom on the multiplicity space of one two-cell.
---

**ESTABLISHED SCOPED GAUGE FENCE.**  Let

```text
G_0 --H_0-- G_1 --H_1-- ... --H_5-- G_0                 (IRH1)
```

be a six-cycle of finite packet groups and edge subgroups.  Suppose the
cycle has one coherent finite-dimensional realization: representations
`pi_i^0:G_i->U(E)` whose restrictions to each `H_i` agree literally.  This
holds, in particular, when the `G_i` are subgroups of one finite group `F`
and `pi_i^0` are the restrictions of `lambda_F`.  Each `pi_i^0` is then a
positive multiple of `lambda_(G_i)`.

After amplification by an arbitrary multiplicity space `K`, put

```text
pi_i=pi_i^0 tensor 1_K.                                  (IRH2)
```

The identity operators are closing edge intertwiners.  More generally, for
every `Z in U(K)`, keep five edge intertwiners equal to the identity and put

```text
T_5=1_E tensor Z.                                        (IRH3)
```

Since `1_E tensor Z` commutes with every packet action, all six edge
intertwining equations remain exact, while the closed product is

```text
Omega=T_5 T_4 ... T_0=1_E tensor Z.                      (IRH4)
```

Thus one isolated regular braid hexagon realizes **every** external
`U(K)`-valued holonomy.  Conversely an external holonomy `1_E tensor Z` is
removed by multiplying any one edge intertwiner by `1_E tensor Z^(-1)`.
There is no scalar, determinant, rank, or full-unitary obstruction carried
by the abstract compatibility gauges of one cell.

For the standard finite `A_2` packet take

```text
F=SL_3(F_q),       G_i=U_i                               (IRH5)
```

with the six ordered upper-unipotent radicals.  Their root occurrences are
literal subgroups of `F`, and `lambda_F|U_i` is
`[F:U_i] lambda_(U_i)`.  Hence `(IRH1)--(IRH4)` applies to the complete
regular Heisenberg packet, not merely to its character or restriction
tables.

The conclusion is deliberately about **compatibility gauges**, not about a
specified group-word occurrence.  A literal Weyl/Whitehead word may fix an
edge transition and remove the freedom in `(IRH3)`, but then the proof must
authenticate that native occurrence.  Calling an arbitrary packet
intertwiner the Weyl word is exactly the selector-occurrence error fenced by
`property-t-free-provenance-delta-2026-08-26`.

Consequently a fixed-radius attack on
`leavitt-regular-character-is-not-mf` cannot use the optimized holonomy of
one isolated regular braid cell.  It must either authenticate a native
transition word or couple the same edge occurrence to other two-cells so
that it can no longer absorb an arbitrary multiplicity correction.

DERIVATION
isolated-regular-a2-hexagon-gauge-proof
