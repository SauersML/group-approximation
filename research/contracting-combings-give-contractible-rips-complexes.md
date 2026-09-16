---
rg: 2
id: contracting-combings-give-contractible-rips-complexes
kind: claim
title: A group with a contracting combing has a contractible Rips complex (Alonso)
distinct_from:
  hyperbolic-rips-complex-models-proper-actions: that is the theorem for hyperbolic groups; this is Alonso's generalization to any group with a contracting combing, which contains the hyperbolic case
  automatic-groups-have-contractible-rips-complexes: that is the open claim for automatic groups, whose combings are only bounded; this is the established theorem for the stronger contracting combings
---

**ESTABLISHED by citation** (route `contracting-combings-give-contractible-rips-complexes-citation`).

Let `G` be finitely generated with a word metric `d`. A *path* is an eventually
constant map `p : N_0 → G` with `d(p(n), p(n+1)) <= 1`. A *combing* is a choice of
path `s(g)` from `1` to `g` for every `g`. It is:

- *bounded* if there is a monotone `φ : N_0 → N` with `φ(n) >= n` and
  `d(s(g)(n), s(h)(n)) <= φ(d(g,h))` for all `g, h, n`;
- *contracting* if there is `C >= 2` such that for all `g, h` and `n' <= n` with
  `⌊C/2⌋ <= n`, `d(s(g)(n), s(h)(n')) <= C` implies
  `d(s(g)(n − ⌊C/2⌋), s(h)(n')) <= C`.

  (Corrected 2026-09-16 from `n <= n'`, which the source does not say and which only
  finite groups satisfy; see
  `research/artifacts/zaremsky-4-01-contracting-combings-2026-09-16.md`, Proposition 1.)

Theorem (Alonso): if `G` admits a bounded combing, then for every `t` there is
`s >= t` such that `VR_t(G) → VR_s(G)` is trivial on every `π_k`. If `G` admits a
contracting combing, then `VR_t(G)` is contractible for some `t`.

Automatic groups have bounded combings with `φ(n) = Cn + D`, so they get only the
first conclusion (type `F_∞`). The gap between bounded and contracting combings is
the gap in Zaremsky Problem 4.1.
