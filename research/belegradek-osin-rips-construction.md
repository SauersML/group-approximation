---
rg: 2
id: belegradek-osin-rips-construction
kind: claim
title: Belegradek--Osin Rips construction with a prescribed hyperbolic source for the kernel
distinct_from:
  rips-kernel-without-finite-quotients: that asks for a Rips extension whose kernel has no nontrivial finite quotient over a non-residually-finite quotient; this is the unconditional construction, which prescribes the kernel only as a quotient of a chosen hyperbolic group.
  rips-kernel-target-iff-hyperbolic-nonrf: that is an equivalence between two existence problems which uses this construction in one direction; this is the construction itself, imported as a theorem.
artifacts:
  - research/artifacts/hyperbolic-leavitt-cover-relative-defect-2026-09-12.md
---

**ESTABLISHED (literature import).** Let `H` be a non-elementary
word-hyperbolic group and let `Q` be a finitely presented group. Then there is
a short exact sequence

```text
1 -> N -> G -> Q -> 1
```

with `G` word-hyperbolic and `N` a quotient of `H`. Moreover, `G` is
torsion-free whenever `H` is.

Source: I. Belegradek and D. Osin, *Rips construction and Kazhdan property
(T)*, Groups Geom. Dyn. **2** (2008) 1--12, arXiv:math/0605553v4,
**Corollary 1.2**. The reviewer lane read the v4 PDF on 2026-09-12; verbatim:
"For any nonelementary hyperbolic group H and any finitely presented group Q,
there exists a short exact sequence 1→N→G→Q→1, where G is hyperbolic and N is
a quotient group of H. Moreover, G is torsion-free whenever H is." The arXiv
abstract, read the same day, states the first sentence. No further hypotheses
are needed.

## Two permanence facts consumers use

These are standard facts about property (T), not part of the import; see
Bekka--de la Harpe--Valette, *Kazhdan's Property (T)*, Chapter 1.

- If `H` is Kazhdan, then `N` is Kazhdan, because it is a quotient of `H`.
- If in addition `Q` is Kazhdan, then `G` is Kazhdan, because an extension of a
  Kazhdan group by a Kazhdan group is Kazhdan.

The construction gives no control over the finite residual of `N`, which is
why `rips-kernel-without-finite-quotients` stays open.
