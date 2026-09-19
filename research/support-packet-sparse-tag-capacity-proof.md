---
rg: 2
id: support-packet-sparse-tag-capacity-proof
kind: route
title: Exhaust the complete allowed and forbidden Wedderburn signatures through five summands
target: support-packet-five-sparse-wedderburn-tag-capacity-is-two
requires:
  - support-packet-covariant-wedderburn-detector
---

`experiments/support_packet_wedderburn_tag_capacity.py` imports the exact
38-irrep character/fusion model already verified by
`support-packet-covariant-wedderburn-detector`.  For every multiset of `r`
irreducibles, it adds the corresponding fusion vectors for all twelve allowed
sources and the unique forbidden source.

For a decomposition

```text
S tensor V = directSum_i m_i T_i,
```

the embedded commutant has unitary-conjugacy signature equal to the sorted
multiset `(m_i,dim T_i)` over nonzero `m_i`.  This is exactly what the script
records.  It groups by coefficient dimension and all twelve allowed
signatures, then counts distinct forbidden signatures.  Exhaustive iteration
uses `combinations_with_replacement(range(38),r)`, so repeated irreducibles
and every coefficient of the stated length are included once.

The checked JSON outputs contain all counts in `(S5C1)` and witnesses for
every maximum class retained by the report.  Since the largest counted set
of forbidden signatures has cardinality two, the asserted sparse capacity
bound follows.  No inference is made outside the enumerated range or after
permuting the twelve allowed source labels.
