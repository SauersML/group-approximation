---
rg: 2
id: fpbs-relative-fixed-price-free-pairs-from-fg-pairs
kind: route
title: Specialize the finitely generated pair inequality to free pairs using fixed price of free groups
target: fpbs-relative-fixed-price-free-pairs
requires:
  - fpbs-relative-fixed-price-fg-pairs
artifacts:
  - research/artifacts/fpbs-relative-fixed-price-decomposition-2026-09-17.md
---

Let `K ≤ L` be nontrivial finitely generated free groups, and let `a` be a
free action of `L`.
- `K` is infinite, so `fpbs-relative-fixed-price-fg-pairs` gives
  `relC(E_{a|L}; E_{a|K}) ≤ (C(E_{a|L}) − C(E_{a|K}))^+`.
- `a|K` and `a|L` are free, so Gaboriau's lecture notes Cor 2.25 ("The
  following groups are strongly treeable and have fixed price:
  C∗(Fn) = C∗(Fn) = n for the free group of rank n.") identifies the costs
  with `rk K` and `rk L`. ∎
