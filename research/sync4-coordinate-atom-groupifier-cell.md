---
rg: 2
id: sync4-coordinate-atom-groupifier-cell
kind: claim
title: Close one common-corner coordinate-reflection cell for the fixed SYNC4 hard family
distinct_from:
  oracular-2csp-mark-relative-canonical-groupifier: that asks to groupify arbitrary oracular 2-CSP marginal sums; this asks only for equality of single coordinate reflections in the fixed one-negative four-character corner.
  hyperoctahedral-reflection-q-overlap-groupifier: that balances a general BCS in a large irreducible signed packet; this uses a four-character commutative packet with arbitrary completeness-side atom multiplicities.
  three-chart-loop-retains-free-multiplicity-holonomy: that proves abstract full transports retain arbitrary multiplicity holonomy; this asks for the nontransport return which kills that residual freedom on the SYNC4 incidence graph.
---

**OPEN.**  Input is a finite `SYNC_4` instance from
`fixed-sync-k-language-is-re-hard`.  At every variable and clause node use
the rational finite-group corner from
`sync4-one-negative-abelian-corner-wordizes-arbitrary-pvm`.  Construct,
effectively, an ordinary recursively enumerable group presentation and a
rational mark `p` such that:

1. every perfect CE `SYNC_4` model yields one exact representation in which
   `p` is nonzero; arbitrary local atom multiplicities must remain allowed;
2. in every canonical-profile matrix ultraproduct where `p` survives, all
   node corners meet one common nonzero carrier `q`, and

```text
r_(clause,j) q = r_(variable,0) q                       (SCG1)
```

   for every incidence `(clause,j,variable)`.

By `sync4-coordinate-atom-normal-form`, `(SCG1)` makes every losing edge zero
exactly, so the normalized corner trace is a perfect CE model of the hard
instance.  No predicate decoder, marginal sum, rank balancing, or
approximation modulus remains.

Independent identifications of the local four-character corners are not
enough.  Their relative multiplicity unitary around a cycle is the escape
isolated by `three-chart-loop-retains-free-multiplicity-holonomy`.  The cell
must therefore use a genuinely nontransport return, a same-block Hecke entry,
or another finite-support group-ring mechanism that forces `(SCG1)` on one
common carrier without imposing equal local atom ranks on the completeness
model.
