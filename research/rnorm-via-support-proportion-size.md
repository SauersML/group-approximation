---
rg: 2
id: rnorm-via-support-proportion-size
kind: route
title: Dead - detect a strict compressor self-embedding of realized twists by the support proportion of realizers
target: relative-normalization-modulo-kazhdan-kernel
requires:
  - support-proportion-size-separates-compressor-images
---

**Dead.** Invalidated by `conjugation-invariant-sizes-miss-relative-defect`.

The plan was a Kun--Thom-style pigeonhole on a measure-type size. Along a
strict compressor self-embedding `eps_t(Q_s) < Q_s`, the support proportion of
realizers would strictly change while `sigma(t)` preserves counting measure.
That is a contradiction, so `eps_t` would be surjective and `sigma(G)` would
normalize `N_rel(sigma)`.

It fails at the first step. Support proportion is a conjugation invariant, and
`eps_t` moves realizer sets by conjugation, so the size never changes. In
trace-zero models, nontrivial host elements have full support anyway. The
premise is refuted.
