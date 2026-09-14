---
rg: 2
id: recursive-residually-finite-non-exact-groups-exist
kind: claim
title: Some finitely generated residually finite non-exact group is recursively presented
distinct_from:
  residually-finite-non-exact-groups-exist: that is Osajda's existence theorem; this adds that his construction is effective, so one such group is recursively presented.
artifacts:
  - research/artifacts/sk-free-1-exactness-2026-09-13-part2.md
---

**ESTABLISHED (unreviewed).** Route: `recursive-residually-finite-non-exact-groups-exist-proof`.

There is a recursively presented, finitely generated, residually finite group without property A, equivalently a non-exact one. It is Osajda's graphical small cancellation group, built from a recursive input sequence of labelled expanders. Each inductive step is a terminating search.

**Review (sk-verify-15, 2026-09-13): PASS-WITH-FIXES.** The construction of arXiv:1703.03791 §3 (e-print l.300–440) was read at source; every choice is a terminating search. F1: take fundamental cycles at every base vertex of the cover for the finite generating set of cycle words. F2: state that the recursive input graphs have girth → ∞, as the non-exactness proof uses. See `research/artifacts/sk-verify-15-2026-09-13-part1.md` §2.
