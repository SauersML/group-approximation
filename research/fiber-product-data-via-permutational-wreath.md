---
rg: 2
id: fiber-product-data-via-permutational-wreath
kind: route
title: Dead -- build the fiber-product data from a permutational wreath product
target: universal-fiber-product-data-for-word-problem-groups
requires: []
artifacts:
  - research/artifacts/boone-higman-fiber-product-and-shift-compiler-2026-08-24.md
---

**Dead.**  Invalidated by
`wreath-base-conjugacy-classes-are-finite-multisets`.

The attempt: embed `G` in `B` for a convenient `B`, take
`T = B wr_S Sym_fin(S)` with `S` infinite and `N = B^{(S)}` the base.  `N` is
normal, the top group is highly transitive so positional invariants of tuples
die, and everything is explicit.  Written with an empty prerequisite list
because if the conjugacy count worked there would be nothing else to check.

It does not work, and not marginally: the `T`-conjugacy classes of `N` are
exactly the finite multisets of nontrivial `B`-conjugacy classes, so the
count is infinite as soon as `B != 1`, whatever `B` and `S` are.  Support
size alone is already an unbounded invariant.

Also worth noting for anyone who repairs the count some other way: `T` here
is not finitely presented either -- `Sym_fin(S)` is not finitely generated
for infinite `S` -- so clause 2 would need separate work.  The conjugacy
count is the one that cannot be repaired within the family.
