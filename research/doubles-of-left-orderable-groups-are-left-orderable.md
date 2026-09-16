---
rg: 2
id: doubles-of-left-orderable-groups-are-left-orderable
kind: claim
title: The double of a left-orderable group along any subgroup is left-orderable
distinct_from:
  doubles-of-surjunctive-groups-are-surjunctive: that transfers surjunctivity to doubles; this transfers left-orderability, and with it unique products and the domain property of every group ring.
  free-group-doubles-over-any-subgroup-are-sofic: that proves soficity of doubles of free groups through a coset-action wreath product; this proves left-orderability of doubles of any left-orderable group through the fold.
  every-noninjective-star-fold-has-kernel-f-infinity: that computes finiteness properties of fold kernels of star amalgams; this only uses that a fold kernel is free to transfer an order.
  kaplansky-zero-divisor-conjecture: that is the conjecture; this is a permanence statement showing that iterated doubling of orderable groups cannot produce a counterexample host.
artifacts:
  - research/artifacts/bengi-wise-doubles-left-orderable-2026-09-16.md
---

Let `A` be a left-orderable group and `C <= A` any subgroup. Let
`\underline A` be a copy of `A` via an isomorphism `a -> \underline a`, and
let

```text
D = A *_{C = \underline C} \underline A
```

be the double, which identifies each `c in C` with `\underline c`. Then `D` is
left-orderable.

More generally, an amalgam `E = A *_C B` is left-orderable if there is a
homomorphism from `E` to a left-orderable group that is injective on `A` and
on `B`. The fold `D -> A` is such a homomorphism for the double.

Consequences:
- free groups are left-orderable (Magnus), so every iterated double of a free
  group along arbitrary subgroups is left-orderable;
- such groups are torsion-free and have unique products;
- their group rings over every field have no zero divisors.

In particular, an iterated double of a free group, or of any left-orderable
group, contains only left-orderable subgroups. The application to Promislow's
group is `bengi-wise-groups-are-left-orderable`.
