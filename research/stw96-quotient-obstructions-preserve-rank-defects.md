---
rg: 2
id: stw96-quotient-obstructions-preserve-rank-defects
kind: claim
title: Quotient-detected generator obstructions cannot repair real or stable rank
artifacts:
  - research/artifacts/stw96-regular-rank-single-generation-audit-2026-08-30.md
---

Let `q:E -> Q` be a surjective *-homomorphism.

1. If `E` has stable rank one, then `Q` has stable rank one.
2. If `E` has real rank zero, then `Q` has real rank zero.
3. If `E` is nowhere scattered, then `Q` is nowhere scattered.
4. If `E` is singly generated, then `Q` is singly generated.

Consequently, a quotient-based proof that `E` is not singly generated cannot
produce the first counterexample in either surviving regularity class: if the
quotient obstruction `Q` is not singly generated and `E` has stable rank one
(respectively real rank zero and nowhere scattered), then `Q` is already a
counterexample with those properties.

In particular, if the Elliott--Li--Niu algebra `A` is a quotient of `E`, then

```text
tsr(E) >= 2,        rr(E) >= 2.
```

Thus none of the nowhere-scattered extensions, obstructed `C(X)`-fields, or
character-tensor amplifications built from `A` can reach stable rank one or
real rank zero.
