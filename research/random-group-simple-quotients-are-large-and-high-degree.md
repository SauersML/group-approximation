---
rg: 2
id: random-group-simple-quotients-are-large-and-high-degree
kind: claim
title: Gromov random groups a.a.s. have no simple quotient of bounded projective degree or of order below exp(ck), although the first moment of each bounded-degree family is infinite
distinct_from:
  density-random-groups-no-finite-quotients-below-exp-k: that excludes quotients below exp(κ_m k) in the cyclically reduced model and says nothing about degree; this works in Kozma–Lubotzky's reduced-word model, excludes every bounded projective degree at every order, and separates a.a.s. absence from the moment
  density-random-simple-quotient-first-moment-diverges: that shows the unconditioned moment of all simple quotients is infinite through alternating targets; this shows the moment of one bounded-degree family, PSL_2(F_p), is infinite while that family is a.a.s. absent, and that conditioned moments are statements about each member
  random-groups-have-no-fixed-degree-linear-representations: that is the imported fixed-degree representation theorem; this is its consequence for finite simple quotients, combined with an order bound and the marked-limit characterization
artifacts:
  - research/artifacts/solve-hyperbolic-rf-simple-quotients-2026-09-13.md
---

**ESTABLISHED** (direct proof; not independently reviewed; no novelty claimed).

**Setting** (as in `random-groups-have-no-fixed-degree-linear-representations`).
- `m >= 2`, and `R` consists of `k = ⌊|S_l|^d⌋` independent uniform reduced words of
  length `l`, with repetitions. Put `Γ = <x | R>`.
- `θ_m = log((2m−1)/(2m−2))` and `M_l = ⌊exp(θ_m k/(2(m+1)))⌋`.
- `X` and `pdeg` are as in `infinite-simple-quotient-count-iff-marked-limit-quotient`.

**THEOREM.**

```text
(Q1) For l >= 2 and every M, P[Γ has a finite simple quotient S with 3 <= |S| <= M]
     <= 2 M^(m+1) ((2m−2)/(2m−1))^k. For d > 0 this is <= 2 exp(−θ_m k/2) at M = M_l.
(Q2) For d > 0 and each fixed D, a.a.s. every finite simple quotient S of Γ with
     pdeg(S) <= D has |S| <= 2, and no infinite quotient of Γ embeds in GL_(D^2)(K) for
     any field K.
(Q3) For d > 0 and each fixed D, a.a.s.: every epimorphism sequence φ_n: Γ ->> S_n as in
     (M1) of the marked-limit claim has pdeg(S_n) > D and |S_n| > M_l for all n.
(Q4) For every odd l >= 3 and every d >= 0, the expected number of normal subgroups of Γ
     with quotient PSL_2(F_p), p >= 5 prime, is infinite, and so is the expected number
     with quotient Alt(n), n >= 5 odd. Yet by (Q2) with D = 2, a.a.s. Γ has no
     PSL_2(F_p) quotient.
(Q5) For every event E of positive probability at fixed l, E[X(Γ) | E] < ∞ iff
     X(Γ_R) < ∞ for every relator sequence R in E.
```

**Reading.**
- **Bounded rank is settled, a.a.s.** Quotients of bounded projective degree are excluded
  in every characteristic and at every order. By standard facts not re-read here, this
  covers exceptional groups and classical groups of bounded dimension.
- **What is left.** A simple quotient that survives is huge and of projective degree
  above any fixed bound. Alternating groups and classical groups of unbounded dimension
  are what remain.
- **The moment is the wrong tool.** Family moments diverge even for families that are
  a.a.s. absent (Q4), and conditioning is per member (Q5). The statement that decides
  Gromov's question is `P[X(Γ) < ∞] > 0` at some `l` with `d < 1/2`, via (C1) of
  `convergent-quotient-count-decides-gromov-question`, together with the a.a.s.
  hyperbolicity of `Γ` quoted in the artifact.
- **Exact gap.** A.a.s. `Γ` should map onto no infinite marked limit of finite simple
  groups of unbounded projective degree. The degree bound in (Q2) is fixed before
  `l -> ∞`, so (Q2)–(Q3) do not give this.

Proof: `random-group-large-high-degree-simple-quotients-proof`.
