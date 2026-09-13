---
rg: 2
id: zaremsky-2-12-loop-braided-v-type-f-infinity
kind: claim
title: "Zaremsky Problem 2.12 resolved: is loop braided V of type F_infinity?"
root: true
distinct_from:
  loop-braided-thompson-group-v-loop-is-type-f-infinity: that claim is the affirmative answer; this claim is the question, established by either answer
  loop-braided-thompson-group-v-loop-is-not-type-f-infinity: that claim is the negative answer; this claim is the question, established by either answer
---

M. C. B. Zaremsky, *Some open problems* (version of July 12, 2026,
https://zaremsky.github.io/open_problems.pdf), Section 2, Problem 12,
verbatim: "Prove “loop braided V ” is of type F∞."

This claim is the question. It is established only through an answer route:

- **Yes**: `zaremsky-2-12-by-yes` requires
  `loop-braided-thompson-group-v-loop-is-type-f-infinity`.
- **No**: `zaremsky-2-12-by-no` requires
  `loop-braided-thompson-group-v-loop-is-not-type-f-infinity`.

Never write a `requires: []` route into this claim.

**Precise reading.** "Loop braided V" is the group `V_loop` of
Witzel–Zaremsky, *Thompson groups for systems of groups, and their finiteness
properties*, arXiv:1405.5491v3, Groups Geom. Dyn. 12 (2018) 289–358, Section
10 (read from the v3 PDF, pp. 53–57):

- `LB_n = ΣAut_n`, the symmetric automorphisms of the free group
  `F_n = ⟨x_1, …, x_n⟩`: every `x_i` is sent to a conjugate of some `x_j`
  (conjugates of inverses are not allowed). `PLB_n = PΣAut_n` is the pure
  version (`x_i` to a conjugate of `x_i`).
- Generators (Fenn–Rimányi–Rourke 1997): `β_i: x_i ↦ x_{i+1},
  x_{i+1} ↦ x_{i+1}^{-1} x_i x_{i+1}` and `σ_i: x_i ↔ x_{i+1}`.
- `ρ_n: LB_n → S_n` sends `β_i` and `σ_i` to `(i i+1)`. The cloning maps
  are formulas (10.1)–(10.2). Lemma 10.1: these define cloning systems on
  `LB_*` and `PLB_*`.
- Theorem 10.2: `V_loop := T(LB_*)` and `F_loop := T(PLB_*)` exist, contain all
  (pure) loop braid groups, and surject onto `V` and `F` respectively.
- Conjecture 10.3, verbatim: "V_loop and F_loop are of type F∞."

The list asks only about `V_loop`. `F_loop` is a companion question with the
same method, and is not part of this root.

**Known inputs.**
- Witzel–Zaremsky Proposition 5.9: for a properly graded cloning system, if the
  `G_k` are eventually of type F_n and the descending-link complexes
  `L_k(G_*)` are eventually (n−1)-connected, then `T(G_*)` is of type F_n.
- The same paper (p. 55) says `LB_n` is of type F∞ because it acts properly
  and cocompactly on the contractible space of marked cactus graphs (Collins,
  Comment. Math. Helv. 64 (1989)).
- The route `v-loop-f-infinity-via-stein-farley-descending-links` records the
  reduction.

Open status: no later answer was found in the arXiv author listings of
Zaremsky and Witzel (checked 2026-09-13; web search was unavailable, so the
check is bounded).

## Attempts

- 2026-09-13 (lane z2-12-loop-bv): the Stein–Farley reduction splits the
  problem into three claims:
  - `loop-braid-groups-are-type-f-infinity` (citation to verify);
  - `loop-braid-cloning-system-is-properly-graded` (hand proof in progress);
  - `loop-braid-descending-links-are-increasingly-connected` (the crux).
