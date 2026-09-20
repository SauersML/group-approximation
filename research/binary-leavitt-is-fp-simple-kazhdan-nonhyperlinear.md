---
rg: 2
id: binary-leavitt-is-fp-simple-kazhdan-nonhyperlinear
kind: claim
title: The binary Leavitt unit group is finitely presented, infinite simple, Kazhdan, integrally acyclic and nonhyperlinear
distinct_from:
  binary-leavitt-unit-group-is-not-hyperlinear: This additionally assembles finite presentation, infinite simplicity, property T and integral acyclicity for the same specified witness, retaining their separate structural inputs.
  nonhyperlinear-existence-is-two-generator-simple: That supplies a possibly infinitely presented simple envelope; this names one group having the entire displayed profile together.
artifacts:
  - research/artifacts/liu-leavitt-direct-internality-and-consequences-2026-09-20.md
  - research/artifacts/khanh-2609-08428-leavitt-gl-verified-2026-09-11.md
  - research/artifacts/liu-leavitt-consequences-audit-2026-09-20.md
---

For R=L_(F_2)(1,2), the SAME group H=R^x is finitely presented, infinite,
simple, has property (T), is integrally acyclic, and is not hyperlinear.
Integral acyclicity means H_n(H;Z)=0 for every n>0. No manageable finite
presentation or effective matrix-obstruction tolerance is asserted here.

## Attribution

The nonhyperlinearity input is the independently checked Cairn application of
Jihao Liu, [*Nonhyperlinear groups exist*](https://jihaoliu.org/ai-results/nonhyperlinear-groups-exist-2026-09-20.pdf)
(2026-09-20), Theorem 1.2/6.7. The Leavitt two-use deduction is the earlier
Cairn argument, now with a direct internality-only simplification, not a theorem asserted in Liu's paper. Finite presentation and integral acyclicity
are the separate Huynh Viet Khanh Theorems 6.1 and 4.4 imports recorded in
`leavitt-unit-group-finitely-presented` and
`binary-leavitt-unit-group-integrally-acyclic`; the other structural results keep
their recorded credits and trust boundaries.

## Attempts

2026-09-20: the route now assembles accepted prerequisites for one named group, including the separate integral-acyclicity input. The nonhyperlinearity prerequisite is established by the Liu chain and reviewed Leavitt deductions. The Khanh preprint remains a distinct imported trust dependency, not a fresh proof here. This avoids the invalid
inference that separate finitely presented and simple existence theorems
automatically give a single finitely presented simple witness.
