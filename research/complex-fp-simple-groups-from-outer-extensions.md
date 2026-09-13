---
rg: 2
id: complex-fp-simple-groups-from-outer-extensions
kind: route
title: Outer-extension universality forces finitely presented simple groups beyond every recursive bound
target: fp-simple-groups-with-arbitrarily-complex-word-problem
requires:
  - decidable-groups-embed-in-outer-extensions-of-fp-simple-groups
  - outer-extension-word-problem-is-kernel-bounded
  - complexity-bounded-host-classes-are-not-universal
---

Fix a recursive `T`. We may assume `T` is non-decreasing: replacing it by
`T+(m) = m + max_(k≤m) T(k)` only enlarges the bound to be beaten.

Suppose every finitely presented simple group has, for some finite generating
set, a word-problem algorithm within `C*T(C*l) + C*l + C` for some `C`. Take any
extension `1 → S → I → Q → 1` of the kind in
`decidable-groups-embed-in-outer-extensions-of-fp-simple-groups`: `S` finitely
presented, simple and nonabelian, so its centre is trivial; `Q` finitely
presented; and `Q → Out(S)` injective.

By `outer-extension-word-problem-is-kernel-bounded`, every such `I` has word
problem in `F(G)` with `G(n) = T(2^n) + 2^n`. This is one recursive function
serving all of them. By `complexity-bounded-host-classes-are-not-universal`
with bound `G`, some two-generated group with solvable word problem embeds in
no such `I`. That contradicts the universality statement.

Hence some finitely presented simple group beats `T`. This is the same
consequence `complex-fp-simple-groups-from-boone-higman` draws from the
conjecture, so the outer-extension route has no complexity advantage over it.
`∎`
