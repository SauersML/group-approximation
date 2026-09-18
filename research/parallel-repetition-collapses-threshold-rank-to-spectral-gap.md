---
rg: 2
id: parallel-repetition-collapses-threshold-rank-to-spectral-gap
kind: claim
title: The n-fold parallel repetition of a unique game has exactly one constraint-walk eigenvalue above 1-gamma when the base game has none but the top one, and at least n otherwise; so on repetition pipelines with n >= r* the threshold-rank NO-side kill reduces to a spectral-gap condition on the base NO instances
distinct_from:
  spectral-gap-no-outputs-cannot-prove-ugc: that is the SDP rounding and class kill in terms of r eigenvalues above 1-gamma; this computes that count on n-fold repetitions and shows only its r = 1 (spectral gap) branch can reach them once n >= r*.
  ug-hardness-deficit-ratio-padding-line: that is a completeness-side invariant of hardness points; this is a spectral computation on repeated outputs.
  low-label-threshold-rank-reductions-cannot-prove-ugc: that counts eigenvalues of the label-extended walk at the YES case; this counts eigenvalues of the constraint walk of repeated games at the NO case.
  anchored-quantum-parallel-repetition: that is a value bound for anchored repetition of entangled games; this is only the spectrum of the classical repeated constraint graph.
artifacts:
  - experiments/ugc-deficit-ratio-2026-09-17/check_repetition_spectrum.py
---

**ESTABLISHED.** Elementary linear algebra. Proof:
`parallel-repetition-threshold-rank-proof`.

*Setting.* `G` is a unique game in two-prover form: left vertices `V_L`, right
vertices `V_R`, none isolated, positive integer weights and permutation
constraints on `[K]`. Write `w(u, v)` for the total weight between `u` and `v`,
and `deg(u)` for the total weight at `u`. The constraint walk
`A(x, y) = w(x, y)/deg(x)` on `V_L ∪ V_R` is the one used in
`spectral-gap-no-outputs-cannot-prove-ugc`. Put
`M(u, v) = w(u, v)/sqrt(deg(u) deg(v))`, a `V_L x V_R` matrix, with singular
values `1 = s_1 >= s_2 >= ... >= 0`, counted with multiplicity over
`min(|V_L|, |V_R|)` indices. The **n-fold repetition** `G^n` has left vertices
`V_L^n`, right vertices `V_R^n`, one edge for each tuple `(e_1, ..., e_n)` of
edges with weight `prod w_(e_t)`, and the coordinatewise permutation on `[K]^n`.
For `0 < gamma < 1`, write `r_gamma(H)` for the number of eigenvalues of the
constraint walk of `H` that are `> 1 - gamma`.

**Theorem.**

1. *(Spectrum.)* `r_gamma(G^n)` is the number of index tuples
   `(i_1, ..., i_n)` with `s_(i_1) ... s_(i_n) > 1 - gamma`.
2. *(Dichotomy.)* Let `m = #{i >= 2 : s_i > 1 - gamma}`. If `m = 0`, then
   `r_gamma(G^n) = 1` and the spectral gap of `G^n` at level `gamma` equals that
   of `G`. If `m >= 1`, then `r_gamma(G^n) >= n m + 1`.
3. *(Calibration of the NO-side kill.)* For every integer `1 <= r <= n` and
   every `0 < gamma < 1`: `r_gamma(G^n) <= r` iff `s_2(G) <= 1 - gamma`. Fix
   `eps0, delta` with `56 eps0 < 1 - delta`. Every pair `(r, gamma)` admissible
   in item 2 of `spectral-gap-no-outputs-cannot-prove-ugc` has
   `18 r^(2/3) (2 eps0)^(1/3) < 1 - delta`, so `r < r* = (1 - delta)^(3/2)/(18^(3/2) sqrt(2 eps0))`.
   Let `Red = Rep_n o Core` output `G^n` for a base game `G` produced by any
   map `Core`, with `n >= r*`. Then a NO output `G^n` has at most `r`
   eigenvalues above `1 - gamma` for an admissible pair **iff** the base
   instance has `s_2(G) <= 1 - gamma` for an admissible `gamma`. So for such
   pipelines the kill says only this: if every NO base instance has
   singular-value gap `1 - s_2 >= gamma` for one admissible `gamma` (every
   admissible `gamma` exceeds `1536 eps0/(1 - delta - 28 eps0)`), then `P = NP`.
   The rank scale `eps0^(-1/2)` never enters.

**What this changes.** The threshold-rank branch of the swarm's NO-side kill
cannot constrain any parallel-repetition amplification with `n >= r*`. That
covers the Rao-style pipelines from a weak gap `1 - eta^2` versus `1 - eta` to a
constant output gap. Rao's projection-game repetition theorem (A. Rao,
*Parallel repetition in projection games and a concentration bound*, ECCC
TR08-013, Theorem 1.4) is stated for `n >= log(1/eta)/(alpha eta^2)`, which is
unbounded as `eta -> 0`, while `r*` depends only on the output gap
`(eps0, delta)`. On such pipelines only the base game's spectral gap is tested, at the
constant level `gamma*`. Base NO instances whose walk has one singular value
above `1 - gamma*` pass it automatically. No property of `Core`, of the
permutations or of the alphabet is used.
