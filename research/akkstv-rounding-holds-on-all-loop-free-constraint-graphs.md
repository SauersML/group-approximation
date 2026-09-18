---
rg: 2
id: akkstv-rounding-holds-on-all-loop-free-constraint-graphs
kind: claim
title: A degree blow-up turns every loop-free weighted unique game into a weighted-regular one with the same optimum and lambda_2 replaced by min(lambda_2, 1), so the AKKSTV rounding and the spectral-gap gate hold on all loop-free hosts, including biregular bipartite ones and every orientation lift of a 2-to-1 game
distinct_from:
  unique-games-on-expanding-constraint-graphs-are-easy: that is the imported rounding, read as applying only to weighted-regular graphs because its quoted proof uses characterization (7); this removes the regularity hypothesis for loop-free graphs by an exact reduction, without reopening the proof.
  spectral-gap-ratio-reductions-cannot-prove-ugc: that states the gate (K1) for loop-free regular YES outputs and lists non-regular outputs as survivor (S1); this closes the loop-free part of (S1), leaving only outputs with loops.
  orientation-lifts-sandwich-2to1-game-values: that proves every orientation lift is a unique game on the same weighted graph with value at most the source; this adds that the lift's completeness is capped by the host's spectral gap unless the source is in P.
artifacts:
  - experiments/ugc-akkstv-regularize-2026-09-17/check_degree_blowup.py
---

**ESTABLISHED.** Route: `akkstv-degree-blowup-proof`.

*Setting.* This is the setting of `spectral-gap-ratio-reductions-cannot-prove-ugc`,
with nonnegative rational weights written in binary. `λ_2` is the second smallest
eigenvalue of the normalized Laplacian, and `C_A` and `X(s)` are as there.

**(B) Blow-up lemma.** Let `U` be a loop-free unique game with weights `w_uv` and
weighted degrees `d_u > 0`, and let `m_u >= 1` be integers. The blow-up
`B_m(U)` has the following structure.

- *Vertices.* The copies `(u, i)` with `i < m_u`.
- *Edges.* For every constraint `(u, v, π)` of weight `w` and every pair `i, j`,
  a constraint `x_(v,j) = π(x_(u,i))` of weight `w/(m_u m_v)`.

It has the following properties.

1. *Value.* `opt(B_m(U)) = opt(U)`.
2. *Spectrum.* The normalized-Laplacian spectrum of `B_m(U)` is that of `U`,
   together with the eigenvalue `1` of multiplicity `sum_u m_u - n`. In
   particular `λ_2(B_m(U)) = min(λ_2(U), 1)` when some `m_u >= 2`.
3. *Regularity.* A copy of `u` has weighted degree `d_u/m_u`. So `B_m(U)` is
   weighted-regular iff `m` is proportional to `d`, for example `m = d` when the
   weights are integers.
4. *Size and loops.* `B_m(U)` is loop-free, with `sum m_u` vertices and at most
   `(sum m_u)^2` constraints.

For a **biregular bipartite** host (degrees `d_A` and `d_B`, unit weights), take
`m = d_A/g` on `A` and `m = d_B/g` on `B`, with `g = gcd(d_A, d_B)`. Then every
copy pair can carry multiplicity `1`: the blow-up is an ordinary multigraph,
regular of degree `d_A d_B / g`, with `|A| d_A/g + |B| d_B/g` vertices.

**(A) AKKSTV on loop-free hosts.** A deterministic polynomial-time algorithm does
the following. It takes a loop-free unique game `U` with `λ = min(λ_2(U), 1) > 0`
and `opt(U) >= 1 − η`, where `λ >= e η`. It outputs a labeling of `U` of value at
least `1 − C_A (η/λ) log(λ/η)`. For a bipartite host, `λ_2 <= 1` always, so
`λ = λ_2`.

**(K1') Gate on loop-free hosts.** Bullet (K1) of
`spectral-gap-ratio-reductions-cannot-prove-ugc` holds with "regular" deleted and
`λ_2` replaced by `min(λ_2, 1)`. That is, fix `s < 1`, and let a polynomial-time
`f` satisfy both:
- `x in L` implies `f(x)` is loop-free, with `min(λ_2, 1) > 0` and
  `min(λ_2, 1) >= X(s)(1 − opt)`;
- `x ∉ L` implies `opt(f(x)) <= s`.

Then `L in P`. This closes survivor (S1) of that claim, except for YES outputs
that carry loops.

**(G) Selector gate.** Fix `s < 1`. Let `R` be a polynomial-time reduction from
`L` to weighted bipartite 2-to-1 games with NO outputs of value `<= s`. Let `o`
be a polynomial-time orientation, in the sense of
`orientation-lifts-sandwich-2to1-game-values`. Suppose every YES output `G`
satisfies

```text
λ_2(G) > 0   and   λ_2(G) >= X(s) (1 − val(U_o(G))).
```

Then `L in P`. **Where every member dies.** At the completeness of the lift, on
the host, before any soundness or selector analysis. The invariant is
`λ_2(host)/(1 − val(U_o))`. No property of the selector's views, witnesses or
certificates enters. So near-perfect selectors (`val(U_o) >= 1 − η'` with
`η' → 0`) are impossible on every host family whose YES spectral gap stays above
`X(s) η'`, unless the source is in `P`.

*Scope, stated exactly.* (G) kills a selector only on hosts whose gap is large
compared with the lift error. It says nothing about hosts with
`λ_2 < X(s) η'`. That is the survivor (S2) regime, where AKKSTV Theorem 2.6
places all UGC hardness anyway.

*Dedupe note.* Worker swarm-0917-w8-w8-ugc-pull independently posted the same
blow-up lemma and the selector corollary, as `degree-blow-up-extends-spectral-gap-gate-to-irregular-hosts`
and `orientation-lift-selectors-need-vanishing-host-gap`. Neither is landed in
this worktree. Whichever lands second should be merged into the first.
