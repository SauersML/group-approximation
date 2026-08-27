---
rg: 2
id: lin-known-infinite-loop-bell-gap-proof
kind: route
title: Feed a syntactically nonhalting machine to Lin's effective Bell-separation reduction
target: lin-explicit-synchronous-bell-gap-game
requires: []
artifacts:
  - research/artifacts/lin-mastel-slofstra-smooth-cover-ingestion-2026-08-23.md
---

Junqiao Lin, *MIPco = coRE*, arXiv:2510.07162v1, proves that the
`1/2`-Bell-test separation promise problem is RE-complete.  In the proof of the
theorem labelled `samevalueREcomplete`, the promised cases are sharpened to

```text
yes: omega_*(G)=omega_co(G)=1,
no:  omega_co(G)=1 and omega_*(G)<=1/2,
```

for synchronous twelfth-level conditionally-linear-samplable games.  The
reduction sends halting machines to the first case and nonhalting machines to
the second.  Lin explicitly notes that prior knowledge of nonhalting, for
example a program containing an unconditional infinite loop, therefore gives
a constructible Bell experiment realizing the separation.

Fix such a loop program and run the effective reduction.  Its finite output is
the game `G_loop`, and the no-case guarantee is exactly `(LBG1)`.  No search for
a separated instance and no undecidable premise is used.

