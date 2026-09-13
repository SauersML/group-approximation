---
rg: 2
id: labbe-ball-legality-is-pairwise-at-radii-two-to-seven
kind: claim
title: Legality of ball patches of Labbé's shift at radii 2 to 7 is decided by pairs of sub-balls and never by single sub-balls; ChJN's incompatibility radius is 3
distinct_from:
  sfts-without-finite-orbits-are-not-residually-finite-actions: That proves aperiodic SFTs have no periodic approximations; this is an exact finite computation of how sub-balls decide legality of ball patches of Labbé's shift, the combinatorial layer of the climbing step for relations.
  minimal-free-sft-full-group-pattern-models-are-exact: That shows infinite validly coloured models reproduce the marked group; this counts finite ball patches whose sub-balls are legal but which are illegal.
artifacts:
  - research/artifacts/fp-simple-relation-climbing-2026-09-13.md
  - experiments/fp-simple-relation-climbing/labbe_lang.py
  - experiments/fp-simple-relation-climbing/labbe_orders.py
---

**ESTABLISHED (exact computation).**

**Setting.** `Omega_U` is Labbé's 19-tile Wang shift (`minimal-aperiodic-wang-shift-exists`).
- `B(r)` is the `ℓ_1` ball of radius `r` in `Z^2`, and `L_(B(r))` is the set of legal patterns on it.
- A pattern `p` on `B(r+1)` has five sub-balls `B(r)+h`, `h ∈ {0, ±e_1, ±e_2}`.

**Statement.**
1. `|L_(B(r))| = 19, 69, 152, 267, 413, 592, 804, 1047` for `r = 0, ..., 7`.
2. **Incompatibility radius.** Some legal `B(R)`-pattern is compatible with its translate by a
   vector of `ℓ_1` length at most 3 for `R = 0, 1, 2`, and none is for `R = 3, 4`. So the radius
   `R_1` of Chornyi–Juschenko–Nekrashevych (arXiv:1602.04255, line 166) is 3. Their generating
   set `𝒯_5` of `D([[Z^2 ~ Omega_U]])` has `2 · 592 = 1184` elements.
3. **Single sub-balls never decide.** For `r+1 = 2, 3, 4, 5, 6, 7` there are illegal patterns on
   `B(r+1)` whose five sub-balls are all legal: 54, 34, 59, 14, 86, 15 of them.
4. **Pairs of sub-balls decide.** For the same radii, a pattern on `B(r+1)` is legal iff its
   restrictions to all ten unions of two sub-balls are legal.

**Why it matters.** ChJN write the finer 3-cycle `T_(p,(0,g,-g))` as nested commutators of
3-cycles on the sub-balls. For `p` as in item 3 that nested word is trivial in the group.
- Item 4 makes each such triviality follow from relations among at most three 3-cycles of the
  coarser radius (artifact, Lemma 3.1 and the remark after it).
- Items 3 and 4 hold only at the radii computed. Relations between two finer generators involve
  sub-balls at larger offsets, and there the artifact's test (T1) is still to be run.

**Proof:** `labbe-ball-legality-is-pairwise-at-radii-two-to-seven-proof`.
