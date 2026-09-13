---
rg: 2
id: left-orderable-non-sofic-via-lodha-moore-group
kind: route
title: If the Lodha--Moore group is not sofic, it is a left-orderable nonsofic group
target: left-orderable-non-sofic-group
requires: [lodha-moore-group-is-not-sofic, lodha-moore-group-is-bi-orderable-and-not-lea]
---

The Lodha--Moore group `G_0` is bi-orderable
(`lodha-moore-group-is-bi-orderable-and-not-lea`), hence left-orderable.  If
`G_0` is not sofic (`lodha-moore-group-is-not-sofic`), then `G_0` itself is a
left-orderable nonsofic group.  ∎

**Why this candidate.**

- *No Kazhdan subgroup.*  `G_0` is bi-orderable, hence locally indicable, so
  this route is not behind Navas's Question 3
  (`infinite-left-orderable-kazhdan-group`).
- *Stronger than the Thompson F candidate on the approximation side.*  `G_0` is
  finitely presented and not LEA, so the cheapest certificate of soficity
  already fails.  `F` is finitely presented too, but no node records whether
  `F` is LEA.
- *Same quotient structure as `F`.*  Every proper quotient of `G_0` is abelian,
  which is the structural input of the permutation-stability dictionary for
  `F` (`thompson-f-sofic-iff-relator-system-unstable`).
