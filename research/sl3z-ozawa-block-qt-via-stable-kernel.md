---
rg: 2
id: sl3z-ozawa-block-qt-via-stable-kernel
kind: route
title: A stable corona trace-kernel is quasitrace-invisible, so linearity descends to the block algebra
target: sl3z-ozawa-block-algebra-quasitraces-are-traces
requires:
  - sl3z-ozawa-corona-trace-kernel-is-stable
  - stw01-stable-algebras-are-bounded-quasitrace-invisible
  - sl3z-ozawa-block-qt-linearity-iff-corona-kernel-invisible
artifacts:
  - research/artifacts/quasitrace-corona-kernel-stability-2026-09-12.md
---

Full proof: `research/artifacts/quasitrace-corona-kernel-stability-2026-09-12.md` §1.

Let `σ` be a bounded 2-quasitrace on the corona `A = B/I`.

1. **Restriction to the ideal.** `σ|_K` is a bounded 2-quasitrace on `K`: the
   quasitrace axioms and the `M_2`-extension condition are inherited by the
   subalgebra `K ⊆ A` (`M_2(K) ⊆ M_2(A)`), and boundedness is inherited. No
   unitality of `K` is used.
2. **Stable ideals are invisible.** If `sl3z-ozawa-corona-trace-kernel-is-stable`
   holds, `K` is a stable C*-algebra, so `σ|_K = 0` by
   `stw01-stable-algebras-are-bounded-quasitrace-invisible`.
3. **Every quasitrace vanishes on `K`.** Steps 1–2 hold for every bounded
   2-quasitrace `σ` on `A`, which is exactly condition (2) of
   `sl3z-ozawa-block-qt-linearity-iff-corona-kernel-invisible`.
4. **Descend.** That equivalence gives condition (1): every bounded 2-quasitrace on
   `B` is a trace.

The route fires only when `sl3z-ozawa-corona-trace-kernel-is-stable` is established;
that claim is open, so `sl3z-ozawa-block-algebra-quasitraces-are-traces` and STW
Problem I stay open. This is the stability analogue of the exact-kernel and
Cuntz-infinitesimal criteria of the corona artifact.
