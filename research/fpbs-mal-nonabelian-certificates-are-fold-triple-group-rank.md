---
rg: 2
id: fpbs-mal-nonabelian-certificates-are-fold-triple-group-rank
kind: claim
title: At every finite level the non-abelian promotion certificate N/<<K cap N>>^L is, up to t-1 tree generators, the deficiency-zero fold triple group T_V = <y_w | y_w = y_{wab^-1} y_{wa}>, so k_u <= d(T_V) <= min(level count, 2-of-3 seed number); cyclic levels give Fibonacci groups, and p-quotient and Schreier certificates reduce to Fox densities at covering levels
distinct_from:
  fpbs-mal-modp-promotion-certificates-are-fox-annihilators: that computes the abelian mod-p certificate k_u; this identifies the full non-abelian certificate group whose mod-p homology is k_u, and shows that p-quotient and finite-index H_1 certificates of it also reduce to k_u (at the same level or at a covering level).
  fpbs-mal-bernoulli-single-stage-floor: that is the open target; this does not decide it and replaces its non-abelian survivor by the rank of one explicit group per level.
  fpbs-mal-fold-closure-exactness: that is about the 2-of-3 closure of fold triples; this puts a group law on the same triples and compares its rank with the closure seed number.
  fpbs-mal-profinite-fold-density-is-finite-percolation: that identifies the profinite seed density with finite 2-of-3 percolation; here the percolation seed number is only an upper bound for d(T_V).
  fpbs-strongly-ergodic-actions-have-fold-seed-floor: that bounds seed density from below on strongly ergodic actions; this is about exact finite-level group identities and which lower-bound certificates for d(T_V) can work.
artifacts:
  - research/fpbs-mal-fold-triple-group-rank-proof.md
  - experiments/fpbs-pushout-level-2026-09-17/tc.py
  - experiments/fpbs-pushout-level-2026-09-17/pushout.py
  - experiments/fpbs-pushout-level-2026-09-17/fib_check.py
  - experiments/fpbs-pushout-level-2026-09-17/fib_check_out.txt
  - experiments/fpbs-pushout-level-2026-09-17/census.py
  - experiments/fpbs-pushout-level-2026-09-17/census_out.txt
---

**ESTABLISHED.** Theorems A, B and C1–C2 are unconditional. C3 is conditional on
the positive-characteristic sofic Lück statement for `u = 1 - c - cb` named in
`fpbs-mal-modp-promotion-certificates-are-fox-annihilators`; unconditionally it
converts any positive Schreier certificate into a counterexample to that
statement. C4 is a precise list of what is not killed. Proofs are in
`research/fpbs-mal-fold-triple-group-rank-proof.md`.

**Setting.**
- `L = F(a,b)`, `c = bab^-2`, `K = <a,c>`.
- A level is a finite transitive right `L`-set `V`, with `H = Stab(v0)` and `t`
  the number of `K`-orbits.
- `M_H` is the normal closure in `H` of the groups `H cap lKl^-1`. At a normal
  level `G = L/N`, `H/M_H = N/<<K cap N>>^L`, the w13 non-abelian certificate
  group.
- The *fold triple group* is
  `T_V = < y_w (w in V) | y_w = y_{wab^-1} y_{wa} (w in V) >`.

**Theorem A (identity).** `H/M_H = T_V/<<y_{w_1}, ..., y_{w_{t-1}}>>`. In
particular `N/<<K cap N>>^L = T_G` when `Kbar = G`. The proof cones off the fiber
product of the Schreier graph with `core(K)` and gauges the type-0 cone edges to
1. The four edge relations then collapse to one fold triple relation per point.

Every level graph with the `a`- and `c`-edges plus `E` extra edges that generates
the stabilizers has `E >= (t-1) + d(H/M_H) >= d(T_V)`. Along free towers
`t/|V| -> 0`, so the non-abelian certificate density is
`d(T_{V_m})/|V_m| + o(1)`.

**Sandwich.** `k_u(V) = dim H_1(T_V; F_p) <= d(T_V) <= min(E, s(V))`, where
`s(V)` is the 2-of-3 seed number of the triples `{w, wab^-1, wa}`. Under
inversion these become the fold triples `{y, ay, by}`.

**Theorem B (cyclic levels).** For `G = Z/n` with `a -> alpha` and
`b -> beta`, `T_G` is the cyclically presented group
`<y_w | y_w = y_{w+alpha-beta} y_{w+alpha}>`. For `alpha = 2, beta = 1` it is the
Fibonacci group `F(2,n)`. Direct coset enumeration of `L/<<K cap N>>^L` gives
`|N/M| = 1, 8, 5, 11, ∞?, 29, ∞?` for `n = 2..8`, which matches `F(2,n)`
exactly.

**Theorem C (class kill for certificates of d(T_V)).**
- C1: every `p`-group quotient of `T_V` has rank at most `k_u(V)`, by Burnside.
- C2: a Schreier certificate from an index-`j` subgroup of `H/M_H` has density at
  most `t/|V| + k_u(V')/|V'|` for a covering level `V'`. The dying step is
  `M_{H'} <= M_H`.
- C3: covers of free-tower levels are sofic approximations of `F_2`. So under
  sofic Lück approximation in characteristic `p` for `u`, every such
  certificate density tends to 0.
- C4 (survivors): twisted `H_1` in low-dimensional irreducible modules (the
  semisimple bound `e_M k_u(V')/(dim M)^2` is too weak) and non-abelian simple
  colorings `Epi(T_V, S)`.

**Census.** Random `S_4`, `S_5`, `PSL_2(5)` and `PSL_2(7)` levels
(`census_out.txt`) are consistent with Theorem A in every row. Examples:
`Q_8` with `k_u(F_2) = 2`, `Z/7`, `Z/5`, a group of order 56 with odd
abelianization, and a perfect group of order 120.

**Consequence for the target.** D0 for Bernoulli, through non-abelian
certificates at finite levels, is now the single question: is
`inf_m d(T_{V_m})/|V_m| > 0` for some free tower? Here `T_{V_m}` is a
deficiency-zero group with one fold triple relation per point, and the only
remaining ways to certify its rank are the C4 classes.
