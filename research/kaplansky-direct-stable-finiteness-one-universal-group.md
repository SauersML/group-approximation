---
rg: 2
id: kaplansky-direct-stable-finiteness-one-universal-group
kind: claim
title: One two-generator finitely presented group tests Kaplansky direct and stable finiteness for all groups
distinct_from:
  kaplansky-three-properties-fixed-fp-torsion-free-tester: that treats domains, idempotents, and two-sided units over torsion-free groups; this treats one-sided inverses in every matrix size and quantifies over all groups.
  subgroup-supported-one-sided-inverse-rigidity: that confines one inverse whose support generates a directly finite subgroup; this is an exact universal tester theorem.
  direct-finiteness-not-inherited-by-quotients: that rules out quotient-based transfers; this uses subgroup heredity and finitely presented colimit stages instead.
  universal-local-approximation-fixed-two-generator-test-group: that uses the same universal container for finite-table approximation properties; this concerns group rings and matrix one-sided inverses.
---

There exists one two-generator finitely presented group `V` such that, for
every field `k`, the following four conditions are equivalent:

1. `k[V]` is directly finite.
2. `k[V]` is stably finite.
3. `k[G]` is directly finite for every group `G`.
4. `k[G]` is stably finite for every group `G`.

The same `V` works for every field. Moreover the all-coefficient assertion
is equivalent to either finite-field test

```text
F[V] is directly finite for every finite field F,
```

or

```text
F[V] is stably finite for every finite field F.
```

Thus Kaplansky direct and stable finiteness, over all groups and all fields,
reduce to countably many group rings of one fixed two-generator finitely
presented group. The host has every finite torsion order and may be chosen
nonsofic and non-MF.

These are exact reductions, not a proof that the test group rings are
directly or stably finite.

**ESTABLISHED 2026-08-30** by
[[kaplansky-universal-group-via-subgroups-colimits-and-finite-fields]].
