---
rg: 2
id: bh-forces-unbounded-fp-simple-wp-complexity
kind: claim
title: Finitely presented simple groups have word problems of unbounded time complexity
root: true
distinct_from:
  uniform-wp-bound-excludes-bh-universal-targets: that is an unconditional theorem about arbitrary target classes, proved here; this is a statement about the single class of finitely presented simple groups, and it is currently only known to follow from Boone-Higman.
  simple-envelope-forces-solvable-word-problem: that says every subgroup of a finitely presented simple group has solvable word problem, an upper-bound statement with no complexity in it; this asserts that no recursive upper bound holds across the class.
  kms-arbitrarily-hard-fp-rf-groups: that realizes arbitrary hardness inside finitely presented residually finite groups, which are never simple when infinite; this asks for the same phenomenon inside finitely presented simple groups, where no example of any high complexity is known.
artifacts:
  - research/artifacts/boone-higman-complexity-wall-2026-09-11.md
---

**OPEN.** For every recursive non-decreasing `g` there is a finitely
presented simple group whose word problem, over any finite generating set, is
not decidable in time `C*g(C*n) + C*n + C` for any constant `C`. Equivalently,
the word problems of finitely presented simple groups are not bounded by any
single recursive function.

The statement is generating-set independent, because a change of finite
generating set is a length-linear substitution and `F(g)` in `(UWB1)` is
closed under those.

## Status and why it is a root

It is a known question, and this graph records it because Boone--Higman
implies it: `bh-unbounded-wp-complexity-proof`. It is a root rather than a
Boone--Higman lane because it is a question about one class of groups with no
embedding statement in it, and because settling it negatively would refute
Boone--Higman.

The tension that makes it interesting is that **every** finitely presented
simple group whose word-problem complexity has actually been determined has
turned out to be easy. The hardest known case is in
[Birget, *The word problem of the Brin--Thompson group is coNP-complete*,
arXiv:1902.03852](https://arxiv.org/abs/1902.03852): the word problem of the
Brin--Thompson group `nV` over a finite generating set is `coNP`-complete for
every `n >= 2`, and each `nV` is finitely presented, infinite and simple.
Nothing in this graph, and nothing found in the literature during this lane,
exhibits a finitely presented simple group whose word problem is provably
harder than that.

## Attempts

1. **Read it off the known finitely presented simple groups.** *Fails for the
   reason just given.* The Thompson-like families have normal forms and their
   word problems sit low; the `coNP`-complete examples are the hardest known,
   and `coNP` is inside `EXP`, hence inside `F(2^n)`. By
   `uniform-wp-bound-excludes-bh-universal-targets`, that family is therefore
   non-universal for Boone--Higman, but non-universality of one family is not
   the unbounded-complexity statement.
2. **Transport hardness from `kms-arbitrarily-hard-fp-rf-groups`.** *Needs
   exactly Boone--Higman.* Those groups are residually finite, hence never
   infinite and simple, so the hardness has to be moved into a simple group by
   an embedding — and a finitely presented simple overgroup of an arbitrary
   decidable finitely presented group is the conjecture. This is the route.
3. **Build a hard finitely presented simple group directly.** *Deferred, no
   mechanism.* The finite-table cover of
   `finitely-presented-nonsofic-group-exists` shows this repository can
   manufacture finitely presented groups with prescribed bad behaviour, but
   simplicity is the adjective none of those constructions delivers, for the
   same finite-normal-generation reason recorded throughout the Boone--Higman
   region.
