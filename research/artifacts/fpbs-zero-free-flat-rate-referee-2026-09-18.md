# Referee pass on the zero-free flat-rate theorem (2026-09-18)

Lane: swarm-0917-w8-w8-bs-last1 (last mile toward
`fpbs-benjamini-schramm-universal`). Target:
`fpbs-zero-free-connectivity-gives-flat-rate`. New route:
`fpbs-zero-free-flat-rate-vitali-proof`.

## 1. Verdict on the 2026-09-17 Harnack proof

Section 2 of `research/artifacts/fpbs-zero-free-connectivity-2026-09-17.md`
was checked line by line. It is correct. Two small repairs are needed; neither
changes a conclusion.

1. **Step 4, "So p <= p_u".** As written this needs monotonicity of
   uniqueness (Haggstrom-Peres), which is not cited. The repair: `a_n` is
   nondecreasing in `p`, so `a_n(p') <= a_n(p) -> 0` for every `p' <= p` in
   `I_+`, and uniqueness fails at every `p' < sup I_+` directly. This is Step 5
   of the new route.
2. **Equation (1.1), `lambda >= rho`.** It is attributed to
   `fpbs-integrated-pivotal-rate-identity`. That is fine, but on bipartite
   Cayley graphs `P(X_n=o)=0` for odd `n`. The new route proves the lower
   bound directly: `a_(n,R)(p) >= P(X_n=o)` for even `n` and
   `>= p P(X_(n-1)=o)` for odd `n`, uniformly in `R>=1`.

The Harnack and Borel-Caratheodory steps are sound but not needed.

## 2. The shorter proof

The new route replaces Steps 1-3 by one observation. By (G) the analytic
`n`-th roots `h_(n,R) = a_(n,R)^(1/n)` (branch positive on `I_-`) are bounded
by `e^M` on `U`. So the whole family indexed by `n>=n_0`, `R>=n` is normal by
Montel. By Schramm's lemma and Kesten, `h_(n,R) -> rho` on `I_-`, uniformly
in `R`. The identity theorem forces every limit to be the constant `rho`, so
`h_(n,R) -> rho` locally uniformly on `U`, jointly in `(n,R)`. Everything
else is read off:

- (a) the modulus at `p` in `I_+`;
- (b) Harris-FKG under uniqueness;
- (c) the Cauchy estimate and the finite Russo identity.

It also sharpens (c): the budget is `o(n)` on compacts of
`I_- union I_+`, not only `O(n)`.

## 3. Imports, each checked

| Import | Where | Used for |
|---|---|---|
| `a_n(p_c) <= rho^n` | `fpbs-critical-walk-correlation` (Schramm's lemma, H18 Prop. 6.4) | limit on `I_-` |
| `rho<1`, `P(X_(2m)=o)^(1/2m) -> rho` | Kesten, Trans. AMS 92 (1959); Woess, *Random walks on infinite graphs and groups*, Sections 1 and 12; limit via Fekete and faithfulness of the trace (in the route) | lower bound, (b) |
| Harris-FKG | standard | (b) |
| Newman-Schulman | standard (0, 1 or infinitely many infinite clusters) | (b) |
| finite Russo identity | Section 1 of `research/artifacts/fpbs/exploration-pivotal-projections.md` | (c) |
| Montel, identity theorem, Cauchy estimate | standard complex analysis | Steps 3, 6 |

## 4. What this does and does not change

- The route `fpbs-zero-free-connectivity-route` now has one open
  prerequisite, `fpbs-connectivity-polynomials-zero-free-around-criticality`
  (hypothesis ZG on every nonamenable Cayley graph).
- Nothing here proves ZG on any graph beyond the tree numerics of the
  2026-09-17 artifact.
- The proof shows that ZG forces, for each fixed `n`, `a_n` on `I_+` to be
  the analytic continuation through `U` of `a_n` on `I_-`, and forces a flat
  rate `lambda = rho` on `I_+`. So ZG fails on any Cayley graph with
  `lambda(p) > rho` for all `p > p_c`. Since `lambda = rho` below
  `p_(2->2)`, such a graph would need `p_c = p_(2->2)`, which would refute
  Hutchcroft's conjecture. No such graph is known.
