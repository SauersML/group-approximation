---
rg: 2
id: fpbs-zero-free-flat-rate-vitali-proof
kind: route
title: Normalize the n-th roots of the zero-free connection polynomials, apply Montel and the identity theorem, then read off the rate, uniqueness and Russo budgets
target: fpbs-zero-free-connectivity-gives-flat-rate
requires:
  - fpbs-critical-walk-correlation
artifacts:
  - research/artifacts/fpbs-zero-free-flat-rate-referee-2026-09-18.md
---

Complete written proof; referee notes on the earlier Harnack proof are in the
artifact. Notation is that of the target claim: `G` a nonamenable locally
finite Cayley graph, `B_R` the induced ball, `X_n` simple random walk from `o`
independent of the percolation, `a_(n,R)(p)=P_p(o <-> X_n inside B_R)`,
`a_n=lim_R a_(n,R)`, `lambda(p)=lim_n a_n(p)^(1/n)`, `rho=||P||`.

**Imports.**

- (K) Kesten: `rho<1` because `G` is nonamenable, and
  `P(X_(2m)=o)^(1/(2m)) -> rho` (H. Kesten, "Symmetric random walks on
  groups", Trans. AMS 92 (1959); Woess, *Random walks on infinite graphs and
  groups*, Section 1 and Section 12). Self-contained for the limit:
  `r_(2m) = P(X_(2m)=o) = ||P^m delta_o||^2` is supermultiplicative in `m`,
  so the limit exists by Fekete, and it equals `||P||` because the spectral
  measure of `delta_o` for the convolution operator `P` has support equal to
  the whole spectrum (its moments are the trace moments, and the trace is
  faithful on the group von Neumann algebra).
- (S) `fpbs-critical-walk-correlation`: `a_n(p_c) <= rho^n` for every `n`
  (Schramm's lemma, [H18, Proposition 6.4]).
- (R) Finite Russo identity for an increasing event `A` of finitely many
  edges: `p (d/dp) P_p(A) = E_p[N_A]`, where `N_A` is the number of open edges
  pivotal for `A`; `N_A>0` forces `A`. Averaged over the independent walk,
  `p a'_(n,R)(p) = E_p[N_(n,R); E_(n,R)]`, that is
  `E_p[N_(n,R)|E_(n,R)] = p a'_(n,R)(p)/a_(n,R)(p)`.
- Montel's theorem, the identity theorem, and the Cauchy estimate.

**Step 1: real two-sided bounds.** Let `0<p<=1`, `n>=1`, `R>=1`.

- Upper: `a_(n,R)(p) <= a_n(p) <= a_n(p_c) <= rho^n` for `p<=p_c`, by
  inclusion of events, monotonicity in `p`, and (S).
- Lower: if `n` is even, `a_(n,R)(p) >= P(X_n=o) =: r_n`, since `o<->o`
  always. If `n` is odd, `a_(n,R)(p) >= p P(X_(n-1)=o) = p r_(n-1)`: on
  `{X_(n-1)=o}` the endpoint `X_n` is a neighbour of `o`, and the edge
  `o X_n` lies in `B_1`, so it is open with probability `p`.

By (K), `(r_n)^(1/n)` and `(p r_(n-1))^(1/n)` tend to `rho`, uniformly for
`p` in a compact subset of `(0,1]`. Hence

    a_(n,R)(p)^(1/n) -> rho   uniformly in R>=1 and in p in compact subsets of (0,p_c],   (1)

and in particular `lambda=rho` on `(0,p_c]`. Also every `r_n` with `n` even
is positive, so `c(J) = inf_(n>=1, R>=1, p in J) a_(n,R)(p)^(1/n) > 0` for
every compact `J` in `(0,1)`.

**Step 2: a normal family of n-th roots.** Assume (Z) and (G) on `U` for
`n>=n_0`, `R>=n`. By (Z) and simple connectivity of `U`, `a_(n,R)` has an
analytic logarithm on `U`; fix the branch `L_(n,R)` that is real at one point
of `I_-`. Since `a_(n,R)>0` on the interval `I_-`, `L_(n,R) = log a_(n,R)`
(real) on all of `I_-`. Put

    h_(n,R) = exp(L_(n,R)/n),   analytic on U,   h_(n,R)^n = a_(n,R).

Then `|h_(n,R)| = |a_(n,R)|^(1/n) <= e^M` on `U` by (G), and
`h_(n,R)(p) = a_(n,R)(p)^(1/n) > 0` for real `p` in `I_-`.

**Step 3: every limit is the constant rho.** Let `(n_k,R_k)` with
`n_0 <= n_k -> infinity` and `R_k >= n_k`. By Montel, a subsequence of
`h_(n_k,R_k)` converges locally uniformly on `U` to an analytic `g`. By (1),
`g = rho` on `I_-`. `U` is connected and `I_-` has accumulation points in
`U`, so `g = rho` on `U` by the identity theorem. Every such sequence has a
subsequence with the same limit, hence

    sup_(R>=n) sup_(z in K) |h_(n,R)(z) - rho| -> 0  (n -> infinity)  for every compact K in U.   (2)

**Step 4: (a).** Let `p` be in `I_+`. `h_(n,R)(p)` is an `n`-th root of
`a_(n,R)(p) > 0`, so `|h_(n,R)(p)| = a_(n,R)(p)^(1/n)`. By (2) with `K={p}`,
for every `eps>0` there is `N` with `a_(n,R)(p) <= (rho+eps)^n` for all
`n>=N` and `R>=n`. Letting `R -> infinity` (the events increase in `R`),
`a_n(p) <= (rho+eps)^n`. With the lower bound of Step 1, `lambda(p) = rho`.

**Step 5: (b).** Let `q = sup I_+ > p_c` and `p' < q`. Since `I_+` is an open
interval there is `p` in `I_+` with `p >= p'`. If `theta(p')>0` and `P_(p')`
had a unique infinite cluster, Harris-FKG would give
`tau_(p')(o,x) >= P_(p')(o <-> infinity, x <-> infinity) >= theta(p')^2` for
every `x`, hence, using monotonicity of `a_n` in the parameter and Step 4,

    theta(p')^2 <= a_n(p') <= a_n(p) <= (rho+eps)^n -> 0,

which is impossible because `rho<1` by (K). If `theta(p')=0` there is no
infinite cluster. So no `p'<q` has uniqueness, and
`p_u = inf{p : uniqueness at p} >= q > p_c`. Each `p` in `I_+` has
`theta(p)>0` and no unique infinite cluster, so by Newman-Schulman it has
infinitely many. This is (b). No monotonicity-of-uniqueness theorem is used.

**Step 6: (c).** Let `J` be a compact interval in `I_- union I_+`; it lies in
one of the two open intervals. Choose `r>0` such that the closed
`r`-neighbourhood `K` of `J` lies in `U`. By (G) and the Cauchy estimate,
`|h'_(n,R)(p)| <= e^M / r` for `p` in `J` and all `(n,R)`. Since
`h' = h L'/n = h a'/(n a)`, (R) gives, for real `p` in `J`,

    E_p[N_(n,R)|E_(n,R)] = p a'_(n,R)(p)/a_(n,R)(p) = p n h'_(n,R)(p)/h_(n,R)(p)
                         <= n e^M / (r c(J)),

with `c(J)>0` from Step 1 (on `J`, `h_(n,R)` has modulus
`a_(n,R)^(1/n) >= c(J)`). So `C_J = e^M/(r c(J))`, uniformly in `n>=n_0`,
`R>=n`. In fact (2) and the Cauchy estimate on `K` give `h' -> 0` uniformly
on `J`, so the budget is `o(n)`: `sup_(R>=n) sup_(p in J) E_p[N|E]/n -> 0`.
QED.

**Remark (what the proof shows beyond the claim).** The joint limit (2) says
the whole family converges to `rho` locally uniformly on `U`, with no
separate `R`-limit. Also the budget in (c) is sublinear, not only linear.
