---
rg: 2
id: cubic-division-congruence-outliers-delocalise-at-log-scale
kind: claim
title: Congruence Schreier graphs of a free pair in SL_1(O_D) are tangle-free at radius c log p, so an outlier eigenfunction has mass O(1/(eps log p)) in every ball of that radius
---

ESTABLISHED (unreviewed; elementary).  Let `D`, `O_D` and `Gamma_D` be as in
`cubic-division-congruence-representations-converge-strongly`, and let `A, B in Gamma_D`
generate a free group `H`.  Fix `D (x) R = M_3(R)` and put
`rho = max ||s||` (operator norm) over `s in {A^(+-1), B^(+-1)}`.  Let `p` not divide `disc(D)`.
Let `X` be a finite `SL_3(F_p)`-set in which every point stabiliser fixes a line of `F_p^3`:
for example `P^2(F_p)`, `F_p^3 minus 0`, the flag variety, or `SL_3(F_p)` itself.  Let `X_p` be the
4-regular Schreier graph of `H` acting on `X` through reduction mod `p`.

1. **Arithmetic tangle-freeness.**  There is a constant `C = C(D, A, B)` such that whenever
   `R < (log p - C) / (144 log rho)`, every ball `B(x, R)` in `X_p` has cyclic fundamental
   group: it contains at most one cycle.
2. **No short cycles of words.**  Let `w != 1` be a word of length `L`.  If `w^d` is regular
   semisimple mod `p`, every point of `P^2(F_p)` fixed by `w^d` is fixed by `w`.  Hence `w` acts
   on `P^2(F_p)` with fixed points and with cycles of length at least
   `(log p - log 64) / (6 L log rho)` only.  For uniformly random permutations and a word that
   is not a proper power, the number of `d`-cycles instead converges to Poisson`(1/d)` for each
   fixed `d` (Nica, 1994; import).
3. **Delocalisation lemma** (any Schreier graph).  Let `X` be a finite 4-regular Schreier graph
   of `F_2 = <A, B>`, `x in X`, `R >= 2`, and suppose `B(x, R)` has cyclic fundamental group.  If
   `sum_s f(s y) = lambda f(y)` for all `y` in `B(x, R)`, and `dist(lambda, [-2 sqrt 3, 2 sqrt 3]) >= eps`,
   then `||f 1_(B(x, R/2))|| <= (8 / (eps R)) ||f 1_(B(x, R+1))||`.
4. **Consequence.**  Put `R_p = (log p - C) / (144 log rho)`.  Every eigenfunction of the adjacency
   operator of `X_p` with `|lambda| >= 2 sqrt 3 + eps` has at most a fraction `64 / (eps R_p)^2` of its
   l^2-mass in any ball of radius `R_p / 2`.  So if half of its mass lies in `K` such balls, then
   `K >= (eps R_p)^2 / 128`.  Outliers, if they exist, are spread over at least order
   `eps^2 (log p)^2` disjoint balls of logarithmic radius.  No local configuration can produce them,
   in any sector of `l^2(SL_3(F_p))`, cuspidal ones included.

**Scope.**  This is the deterministic half of the Friedman--Bordenave argument for random
graphs.  The other half, high-trace cancellation, is the open part
(`cubic-division-free-pair-p2-schreier-asymptotically-ramanujan` and its Ihara--Bass form
`cubic-division-ihara-traces-count-roots-mod-p`).  Tangle-freeness alone bounds no norm: two
expanders joined by a few edges are tangle-free and have an eigenvalue near 4.  Part 4 turns
the "localised outliers" sketch in the open claim's Attempts into a theorem with an explicit
rate.

Proof: `cubic-division-congruence-outliers-delocalise-at-log-scale-proof`.
