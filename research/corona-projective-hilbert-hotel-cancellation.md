---
rg: 2
id: corona-projective-hilbert-hotel-cancellation
kind: claim
title: No nonzero finite projective matrix-corona module is isomorphic to two copies of itself
artifacts:
  - research/corona-projective-hilbert-hotel-cancellation-proof.md
---

If `P` is a finitely generated projective right module over a norm matrix
corona `Q_d`, then

```text
P ~= P directSum P   implies   P=0.
```

More generally, if `P` is isomorphic to the direct sum of `m>=2` copies of
itself, then `P=0`.  Equivalently, no nonzero stable projection in `Q_d` is
infinite or properly infinite.

If a unital ring `R` contains a binary Leavitt family, every unital action

```text
R -> End_(Q_d)(P)
```

on a finitely generated projective `Q_d`-module forces `P=0`.
