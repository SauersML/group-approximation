---
rg: 2
id: sync4-coordinate-atom-groupifier-cell
kind: claim
title: Close one common-corner coordinate-reflection cell for the fixed SYNC4 hard family
distinct_from:
  oracular-2csp-mark-relative-canonical-groupifier: that asks to groupify arbitrary oracular 2-CSP marginal sums; this asks only for equality of single coordinate reflections in the fixed one-negative four-character corner.
  hyperoctahedral-reflection-q-overlap-groupifier: that balances a general BCS in a large irreducible signed packet; this uses a four-character commutative packet with arbitrary completeness-side atom multiplicities.
  three-chart-loop-retains-free-multiplicity-holonomy: that proves abstract full transports retain arbitrary multiplicity holonomy; SYNC4 reads only one atom per incidence, so this asks for selected-atom agreement without requiring full-chart holonomy collapse.
  literal-sync4-c2-amalgam-has-zero-selected-meet: that proves equality of the selected literal reflection leaves the two packet carriers disjoint already on one edge; this asks for the extra non-Bass--Serre carrier correlation.
  one-hot-central-character-selector-forces-weight-three-ghost: that rules out repairing the one-edge meet by one common central-character selector while retaining arbitrary atom multiplicities; this permits a noncentral or genuinely coupled carrier.
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

Independent free amalgams of the local four-character corners are not
enough: they need not leave any common carrier.  However, unlike a generic
full-chart atlas, this cell does **not** need to synchronize the three
unselected atoms.  Once `(SCG1)` holds on one common `q`, every verifier row
is already exact and complementary chart gauges are semantically invisible.

Two exact computations now sharpen this further.  First,
`literal-sync4-c2-amalgam-has-zero-selected-meet` shows that amalgamating the
two selected literal reflections makes their one-negative packet
projections have zero meet already on one edge.  The cell must therefore
create a genuine non-free packet correlation, not merely identify the
reflection words.  Second, even after a common carrier is supplied, the
stabilizer of one atom is `U(H) x U(M_3(H))`.
`sync4-singleton-stabilizer-retains-m3-hecke-holonomy` gives an explicit
two-piece Laurent group-ring unitary realizing a nontrivial complementary
cycle return.  This return is verifier-blind and need not be consumed.
Accordingly the load-bearing target has collapsed to the first job alone:
create positive canonical packet overlap and impose the selected-reflection
equalities there without restricting completeness-side atom multiplicities.

A common finite central-character label is not enough.
`one-hot-central-character-selector-forces-weight-three-ghost` shows that
the character ratios required to realize the deterministic one-hot PVMs
produce a weight-three character in the same selected sector.  The missing
positive correlation must therefore be noncentral, representation-dependent,
or implemented by a genuinely non-character corner coupling.
