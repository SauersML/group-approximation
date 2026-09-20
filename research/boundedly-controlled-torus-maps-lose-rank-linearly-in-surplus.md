---
rg: 2
id: boundedly-controlled-torus-maps-lose-rank-linearly-in-surplus
kind: claim
title: A continuous map between finite products of tori whose inputs are each controlled by at most K outputs loses first-cohomology rank at most c/(1-c) times its surplus, with no locality hypothesis
distinct_from:
  local-rectangular-small-fibre-maps-lose-proportional-rank: that is the conjectured lemma with both locality (L) and control (C); this proves its linear form from (C) alone, with explicit constant C = c_{dK}/(1-c_{dK}).
  sofic-torus-c2-reduces-to-rectangular-small-fibres: that is the reduction of sofic C2 to LRSF; this supplies the group-free input the reduction needs.
  lef-groups-are-torus-surjunctive: that contains the square case (Theorem 1) and the uncontrolled counterexample (Theorem 3); this is the rectangular, boundedly controlled case, proved by a relative cup-length count on fibre neighbourhoods.
artifacts:
  - research/artifacts/controlled-torus-rank-cup-length-2026-09-20.md
---

**Statement (Theorem R).** Let `g: T^n -> T^N` be continuous. Suppose every input
coordinate `i` has a set `C_i` of at most `K` output coordinates such that
`eta`-closeness of `g(u), g(u')` on `C_i` forces `|u_i - u'_i| < 1/16`. Let
`r = rank g^*` on `H^1(T^N; Z) -> H^1(T^n; Z)`, `L = n - r` and `D = N - r`. Then

`L <= c_K D`, equivalently `rank g^* >= n - (c_K / (1 - c_K)) (N - n)`,

where `1/c_K = max_{0<p<1} (1-p)^(K-2) (1 + (K-1)p)`. So `c_2 = 1/2`, `c_3 = 8/9`,
`c_4 = 243/256`, and `c_K < 1` for every `K`. For `d`-dimensional sites
(`g: (T^d)^I -> (T^d)^J` with site control by `K` sites), apply this with `dK`.

**Consequences.**
- The linear form of LRSF holds, *without* the locality hypothesis (L), with
  `C(K, d) = c_{dK} / (1 - c_{dK})`. Hence LRSF holds with
  `beta = delta (1 - c_{dK}) / c_{dK}`.
- With `sofic-torus-c2-reduces-to-rectangular-small-fibres`, every injective torus
  automaton over every sofic group has regular degree and is surjective. This
  consequence inherits that reduction's status (agent-verified only) and should be
  re-audited together with this node.

**Why this does not contradict [LEF] Theorem 3.** The small-ball injection
`T^(N-1) -> T^N` needs control sets of size about `N`. Here `K` is fixed, and
`c_K -> 1` as `K -> infinity`, so the bound degenerates exactly as it must.

**Proof idea.** Fix a random private set `T` of output coordinates.
- On a neighbourhood of a fibre of the row characters, all outputs lift to `R`.
- The `Z`-projection of the kernel directions has dimension at most `D - delta(T)`.
- An Ostrand cover of a polyhedron of that dimension gives `D - delta(T) + 1` open
  families on which the controlled input classes vanish.
- `r` arc sets kill the row classes. The relative cup product then shows that at most
  `D - delta(T)` input classes that are independent modulo the row span can be
  controlled inside `T`.
- Averaging over `T` with density `p` gives `L f_K(p) <= (1-p) D`.

**ESTABLISHED 2026-09-20** by
[[boundedly-controlled-torus-rank-loss-proof]].
Agent-verified only.
