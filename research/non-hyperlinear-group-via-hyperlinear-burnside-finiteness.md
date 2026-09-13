---
rg: 2
id: non-hyperlinear-group-via-hyperlinear-burnside-finiteness
kind: route
title: A large odd exponent free Burnside group is non-hyperlinear if hyperlinear bounded-exponent groups are finite
target: non-hyperlinear-group
requires:
  - hyperlinear-fg-bounded-exponent-groups-are-finite
  - free-burnside-large-odd-exponent-is-nonamenable
---

Take `m = 2` and an odd `N` large enough that `B(2,N)` is non-amenable, hence
infinite (`free-burnside-large-odd-exponent-is-nonamenable`). `B(2,N)` is
finitely generated, of exponent dividing `N`. If it were hyperlinear,
`hyperlinear-fg-bounded-exponent-groups-are-finite` would make it finite, and
it isn't. So `B(2,N)` is non-hyperlinear.

For each `(m,N)`, the requirement is equivalent to trace rigidity of
approximate exponent-N unitary models
(`hyperlinear-bounded-exponent-trace-rigidity-iff-finiteness`). The
Hilbert--Schmidt exponent-law stability route toward Weiss's Open question
9.4 therefore meets exactly this requirement.
