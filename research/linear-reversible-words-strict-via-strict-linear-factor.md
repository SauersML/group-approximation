---
rg: 2
id: linear-reversible-words-strict-via-strict-linear-factor
kind: claim
title: A strict composite of square linear automata and bijective automata over F_q has a strict linear factor
distinct_from:
  low-degree-strict-automata-force-matrix-kaplansky-failure: that handles one polynomial pair of bounded degree product; this handles words of unbounded degree in which all nonlinearity is reversible.
  stable-finiteness-failure-refutes-surjunctivity: that turns a one-sided inverse pair into a strict linear automaton; this extracts a strict linear factor from any strict word in linear and reversible pieces.
artifacts:
  - research/artifacts/low-degree-strict-pairs-linear-parts-2026-09-12.md
  - research/artifacts/gk-vf-nonlinear-verification-2026-09-12.md
---

Let `tau = W_1 ... W_n` act on `F_q^m` configurations over a group `G`. Each factor is either a
square linear automaton over some `F_q^r` or a bijective automaton, of any degree. Cellwise
permutations such as `x -> x^3` on `F_8` count as bijective. If `tau` is injective and not
surjective, some linear factor is injective and not surjective. So `M_r(F_q[G])`, and
`M_(rk)(F_p[G])`, is not directly finite.

**Why.** Induct from the right: `S_(j+1)` surjective and `tau` injective force `W_j` injective.
A bijective factor keeps `S_j` surjective. An injective square linear factor is either surjective
or strict. Since `tau` is not onto, some factor is strict.

**Screen.** Designs built as reversible nonlinear functions wrapped around linear idempotent
projections are Kaplansky pairs in disguise. With rectangular linear factors (window gathering)
every automaton is presented, so the statement cannot extend there. A new mechanism needs a
non-bijective nonlinear step with decoder degree product at least `q`
(`low-degree-strict-automata-force-matrix-kaplansky-failure`).

Proof: Section 8 of the artifact.
