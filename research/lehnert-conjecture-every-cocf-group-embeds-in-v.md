---
rg: 2
id: lehnert-conjecture-every-cocf-group-embeds-in-v
kind: claim
title: "Lehnert's conjecture: a finitely generated group is coCF iff it embeds in Thompson's group V"
artifacts:
  - research/artifacts/zp-lehnert-2-16-2026-09-13.md
---

A finitely generated group has context-free co-word problem if and only if it
embeds as a finitely generated subgroup of Thompson's group `V`. The "if"
direction is known (`V` is coCF by Lehnert–Schweitzer, arXiv:math/0507090, and
coCF passes to f.g. subgroups); the "only if" direction is the open conjecture,
due to Lehnert and put in this form by Bleak–Matucci–Neunhöffer (arXiv:1312.1855,
who showed `QAut(T_{2,c})` embeds in `V`). This is the backdrop of Zaremsky
Problem 2.16 (`zaremsky-2-16-lehnert-conjecture`); a finitely generated coCF
group embedding in no `V` refutes it.

## Attempts

- Positive evidence: all known coCF groups embed in `V` — Bodart–D'Angeli–
  Perego–Rodaro, arXiv:2608.02111 (Aug 2026), which reduces the conjecture to
  "every coCF group admits a faithful context-free action (is CF-TR)".
- Candidate counterexamples: the `V_(G,θ)` with `θ ≠ id`
  (`twisted-direct-power-cloning-finite-groups-are-cocf`) and Farley's FSS
  subfamily (arXiv:1406.4590) — coCF, no obvious faithful Cantor-space action.
- Obstruction calculus: period growth is monotone under embedding and is
  `⪯ exp(n^4)` for coCF groups and `≍ exp(n^2)` for `V`
  (Bishop–Bodart–Issini–Perego, arXiv:2601.13058, Thm 2.7, 6.2); no separation
  yet found. Not attacked further by this lane.
