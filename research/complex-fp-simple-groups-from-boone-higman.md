---
rg: 2
id: complex-fp-simple-groups-from-boone-higman
kind: route
title: Embed the hard graph-shift groups by the conjecture and read off complex simple hosts
target: fp-simple-groups-with-arbitrarily-complex-word-problem
requires:
  - boone-higman-conjecture
  - complexity-bounded-host-classes-are-not-universal
artifacts:
  - research/artifacts/boone-higman-self-similar-and-complexity-2026-09-11.md
---

Fix a recursive `T`. Suppose every finitely presented simple group has a
word-problem algorithm within `C*T(C*l) + C*l + C` for some `C`. Then the class
`K` of all finitely presented simple groups satisfies the hypothesis of
`complexity-bounded-host-classes-are-not-universal`, so some two-generated
group with solvable word problem embeds in no member of `K`. This contradicts
`boone-higman-conjecture`. Hence some finitely presented simple group beats
`T`. `∎`
