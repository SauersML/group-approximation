---
rg: 2
id: central-character-regular-flow-defeats-finite-d8-return
kind: claim
title: A common central character retains a finite regular flow through every finite packet graph
distinct_from:
  finite-packet-graph-atlases-have-a-regular-stationary-flow: that balances the full regular representations; this proves that selecting the negative character of the common D8 center does not remove the stationary countermodel.
  finite-normalizer-star-no-go: that treats one finite packet and its automorphism normalizers; this treats arbitrary finite graphs of finite groups and arbitrary injective edge attachments preserving a common center.
  single-triangle-trace-cyclic-return-cell: that asks for a nonflat two-cell acting on the remaining chord intertwiner; this proves that the selected D8 carrier plus all one-dimensional incidence data still cannot supply that two-cell.
---

Let `Y` be a finite connected graph of finite groups.  Suppose a finite
abelian group `Z` is embedded centrally in every vertex group `G_v` and in
every edge group `H_e`, and that both edge embeddings are the identity on
`Z`.  Fix a character `chi in Z^` and write

```text
q_chi=|Z|^(-1) sum_(z in Z) conjugate(chi(z)) z.       (CCF1)
```

There is a nonzero finite-dimensional representation of the fundamental
group of the graph of groups on which `Z` acts by `chi`.  More precisely,
choose a common integer `L` divisible by every `|G_v|` and put

```text
V_v=(L/|G_v|) q_chi l2(G_v).                           (CCF2)
```

All `V_v` have dimension `L/|Z|`, and on either endpoint of every edge

```text
Res_(H_e) V_v
  isomorphic to (L/|H_e|) q_chi l2(H_e).               (CCF3)
```

Thus the edge restrictions match simultaneously.  Tree-edge intertwiners
and arbitrary chord intertwiners give the asserted finite-dimensional
representation.

For a common central involution `K`, take `Z=<K>` and the negative
character.  Then

```text
H=(1-K)/2
```

acts as the identity on the representation `(CCF2)`.  Consequently no
finite graph of finite packet groups preserving the D8 center can force the
trace-`1/8` holonomy projection to vanish, even after selecting its negative
central sector.  A single HNN stable letter gives the same countermodel.

Direct sums of the character-sector flows independently prescribe any
rational distribution on `Z^`.  In particular, one negative copy and seven
positive copies give

```text
tr((1-K)/2)=1/8,             tr(K)=3/4,                (CCF4)
```

while retaining exact incidence along every edge.  Thus adding only the two
displayed D8 moment tests does not remove the countermodel.  Additional
noncentral packet moments may of course select a narrower profile; the
theorem says that central-character selection and incidence matching alone
never do so.

This closes a possible loophole in the ordinary regular-flow objection:
passing from the full packet regular representation to the selected D8 spin
sector does **not** remove stationarity.  A viable trace-cyclic return must
therefore constrain the chosen chord intertwiner by a genuinely nonflat
two-cell.  It cannot be assembled from finite packet restriction tables,
central-character selection, tree normalization, or Bass--Serre incidence
alone.
