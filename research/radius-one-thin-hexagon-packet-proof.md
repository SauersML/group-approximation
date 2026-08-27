---
rg: 2
id: radius-one-thin-hexagon-packet-proof
kind: route
title: Count the omitted central sectors and the retained twisted irreducibles
target: radius-one-hexagon-probe-omits-regular-packet
requires: []
---

The truncated coefficient space in the script has the seventeen displayed
monomials and the single relation `1=e_00+e_11`, hence `dim(W)=16`.  With two
copies of `V=F_2^5`, the corresponding Heisenberg group has order

```text
2^(5+5+16)=2^26.                                      (RHP1)
```

Fix a central character `psi in W^*`, and let the induced bilinear pairing
`B_psi:V times V->F_2` have rank `r`.  The `psi`-sector of the regular
representation is the twisted regular module of `V times V`, of dimension
`2^10`.  It contains `2^(10-2r)` irreducibles of dimension `2^r`, each with
regular multiplicity `2^r`; indeed

```text
2^(10-2r) * 2^r * 2^r = 2^10.                        (RHP2)
```

For each `chi in V^*`, the script instead chooses one extension `psi_chi`
and retains `2^(5-r)` paired irreducibles once.  Its retained dimension is

```text
2^(5-r) * 2^r = 2^5=32                               (RHP3)
```

in that chosen sector.  There are only `2^5=32` choices of `chi`, so the
whole local packet has dimension `32*32=1024`.  Its construction gives each
incoming and outgoing `(V directSum V)` character once, which explains why
both wall restrictions are regular and why the block gauges describe the
full intertwiner freedom for this prescribed bundle.

But `(RHP2)` occurs for every one of the `2^16` central characters in the
regular Heisenberg representation.  The script samples only `32` of them
and uses `(RHP3)` rather than the full sector.  Amplification cannot alter
this support.  Finally, no generator matrix for the marked central root is
constructed or tested, so holonomy closure alone has no marked-survival
content.  These dimension and support comparisons prove the claim.
