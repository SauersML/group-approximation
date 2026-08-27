---
rg: 2
id: km-triangle-local-bimodules-have-finite-nonflat-models
kind: claim
title: Kac-Moody triangle local regular bimodules admit exact finite nonflat counterpackets
distinct_from:
  finite-graph-of-groups-representation-types-are-integer-flows: that classifies vertex multiplicity vectors for a graph of finite groups; this uses the actual triangle relator kernel and preserves exact regular charts at all three rank-two vertices while one chosen kernel cycle remains nontrivial.
  three-chart-loop-retains-free-multiplicity-holonomy: that inserts an arbitrary spectator in abstract full chart transports; this constructs the counterpacket from finite quotients of the native tree-first Kac--Moody presentation.
  triangle-kernel-relators-charge-authenticated-corner-leakage: that shows the missing kernel relation pays leakage after a common corner is compiled; this proves that local finite-subgroup matrix units and pairwise overlap intertwiners cannot compile that corner by themselves.
---

**ESTABLISHED.**  Use the triangle notation

```text
G_0=P_12 *_(P_2) P_23,
E=P_1 *_(P_0) P_3 <=G_0,
N=ker(E ->> P_13).
```

For every `1!=n in N` there is an exact finite-dimensional packet with:

1. regular-multiple representations of `P_12`, `P_23`, and `P_13`, all in
   one common dimension `D`;
2. exact unitary overlap intertwiners on `P_1`, `P_2`, `P_3`, and hence all
   their finite group-algebra matrix units;
3. identical Plancherel multiplicities on the two sides of every overlap;
4. an unavoidable nontrivial fundamental-cycle holonomy: the pairwise
   overlaps cannot be restrictions of one common chart identification.

The obstruction can be made scalar and carrier-free.  Gauge the finite coset
incidence graph along a spanning tree and multiply one chord intertwiner by
`zeta I`, `zeta!=1`.  This preserves every local finite-subgroup matrix unit
and overlap equation while making that fundamental-cycle holonomy `zeta I`.
It is nontrivial on every nonzero subprojection, in every common
amplification.

More concretely, the `P_12--P_2--P_23` side extends to an exact
representation of `G_0` in which `n` is nonidentity, while the `P_13` side
kills `n`.  A common identification would intertwine `P_1 union P_3` and
hence all of `E`, contradicting those two evaluations.  Thus no rule using
only the three local finite-group tables,
their regular multiplicities, and independently chosen pairwise overlap
maps can produce a common carrier on which the two realizations of `n`
agree uniformly for all such local packets.

The counterpacket is finite-dimensional and remains so after arbitrary
common amplification.  It does not satisfy the missing native face relation
`n=1`; that is precisely the point.  Combined with
`triangle-kernel-relators-charge-authenticated-corner-leakage`, it gives an
exact boundary for the Kac--Moody route: the kernel relator has sufficient
analytic strength, but its compressed coefficient identity cannot be
recovered from local regular bimodule data alone.
