---
rg: 2
id: thompson-f-not-automatic-via-amenable-rigidity
kind: route
title: If F is amenable and amenable automatic groups are virtually abelian, then F is not automatic
target: thompson-f-is-not-automatic
requires:
  - thompson-f-is-amenable
  - amenable-automatic-groups-are-virtually-abelian
  - thompson-f-has-infinite-cohomological-dimension
---

Suppose `F` is amenable (`thompson-f-is-amenable`) and automatic. By
`amenable-automatic-groups-are-virtually-abelian`, `F` has a finite-index
abelian subgroup `A`. `F` is finitely generated, so `A` is finitely generated
abelian, and torsion-free because `F` is, say `A ≅ Z^r`.

By `thompson-f-has-infinite-cohomological-dimension`, `F` contains `Z^n` for
every `n`. Then `Z^n ∩ A` has finite index in `Z^n`, so it is free abelian of
rank `n`. It is also a subgroup of `Z^r`, so `n <= r`. Taking `n = r + 1` gives
a contradiction. So `F` is not automatic.

The prerequisites are two open problems (Zaremsky Problem 2.1 in one direction,
and a universal rigidity statement about automatic groups) plus an established
fact. Neither open prerequisite is equivalent to the target: `F` could be
non-automatic and non-amenable, or non-automatic while some amenable automatic
group fails to be virtually abelian.
