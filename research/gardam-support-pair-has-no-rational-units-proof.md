---
rg: 2
id: gardam-support-pair-has-no-rational-units-proof
kind: route
title: Exact Groebner basis over Q plus a characteristic-free sub-support check
target: gardam-support-pair-has-no-rational-units
requires: []
artifacts:
  - research/artifacts/gardam-support-pair-rational-units-2026-09-12.md
  - research/artifacts/gardam-support-pair-gsp.py
  - research/artifacts/gardam-support-pair-z3-subsets.py
  - research/artifacts/gardam-support-pair-gb-easy.py
---

Write `S = (g_1, ..., g_21)` and `T = (h_1, ..., h_21)`. The equations
`u v = 1` for `u in K^S` and `v in K^T` are the 121 bilinear coefficient
equations built by `gardam-support-pair-gsp.py`. That script first rechecks
Theorem A exactly in `Z[s,t]/<s^4+1, t^4+1>[P]`, so the sets and the product
table are the ones that carry Gardam's unit.

**Step 1: reduction to `u_1, u_2 != 0`.** Let `u` be a nontrivial unit on
`(S,T)` over any field, with `S' = supp(u)` and `T' = supp(u^(-1))`. Then
`|S'| >= 2`, the identity lies in `S'T'`, and no other element of `S'T'` has
exactly one representation `g_i h_j`, because that coefficient of `u u^(-1)`
would be the single nonzero product `u_i v_j`. The z3 query in
`gardam-support-pair-z3-subsets.py` asks for such `(S', T')` with `g_1` or
`g_2` missing from `S'`, and returns `unsat`. As a sanity check, the same
query without that condition returns `sat` with the full pair `(S, T)`. So
`u_1` and `u_2` are nonzero.

**Step 2: the localized system.** Scale `u` so that `u_1 = 1`, and put
`w = u_2^(-1)`. Then `(u, v, w)` is a `K`-point of the ideal
`I = <uv - 1 coefficients, u_1 - 1, u_2 w - 1>` in
`Q[u_1..u_21, v_1..v_21, w]`. Conversely, every point of `I` is such a unit.
`gardam-support-pair-gb-easy.py` (Sage 10.7, Singular `slimgb` over `Q`, exact
rational arithmetic) computes a basis `G` of `I` and reports:

- `G` has 83 elements with coefficients `+-1`, and equals Gardam's
  `groebner_basis.txt`;
- `G` satisfies Buchberger's criterion over `Q`, and all 123 generators of
  `I` reduce to 0 modulo `G`;
- `I` is zero-dimensional with `dim_Q Q[x]/I = 16`;
- the elimination ideal of `I` in `Q[u_7, u_10]` is
  `<u_7^4 + 1, u_10^4 + 1>`;
- `I` has no rational point and no real algebraic point.

Every `Kbar`-point therefore has `u_7^4 = -1`. So `u_7 in K` is a primitive
eighth root of unity. Over `Qbar`, projection of `V(I)` onto `(u_7, u_10)`
maps onto the 16 points of `V(u_7^4+1, u_10^4+1)`, and `dim_Q Q[x]/I = 16`.
So `V(I)` consists of exactly 16 reduced points. QED

**Trust surface.** Singular's `slimgb` over `Q` is exact. The Buchberger
criterion and the reduction of the generators were checked in the same run.
The inclusion `<G> in I` rests on `G` being computed from the generators by
Singular. The z3 verdict in Step 1 carries no proof certificate. The artifact
cross-checks Case B and eight trivial residues independently by 2-adic lifting
(Section 4), with no Groebner basis and no SAT solver.
