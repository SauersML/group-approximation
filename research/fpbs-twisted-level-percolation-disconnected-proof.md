---
rg: 2
id: fpbs-twisted-level-percolation-disconnected-proof
kind: route
title: Count self-avoiding return paths through isolated t-components with Osin's relative area bound, and pay delta per two edges along each path
target: fpbs-twisted-level-percolation-disconnected-at-low-density
requires:
  - hyperbolic-group-relative-to-maximal-elementary-subgroup
  - osin-isolated-components-bounded-by-relative-area
artifacts:
  - research/artifacts/fpbs/docs/twisted-level-percolation-low-density-disconnection.md
---

Written derivation. Full details are in the artifact (Sections 3 and 4).

1. **The peripheral subgroup.**
   - `E(t)` is torsion-free and virtually cyclic, hence `<tau>` with `t = tau^k`.
   - `t` maps to a generator of `Gamma/N = Z`, so `k = +-1` and `E(t) = <t> =: H`.
   - So `H ∩ N = {e}`, and distinct elements of `N` lie in distinct left cosets of `H`.
   - The centralizer of `t^j`, `j != 0`, lies in `H`. So for `x in N \ {e}` the map `m -> phi^-m(x) = t^-m x t^m` is injective.
   - By `hyperbolic-group-relative-to-maximal-elementary-subgroup`, `Gamma` is hyperbolic relative to `{ {1}, H }`. That is a finite relative presentation with a linear relative Dehn function.
   - Enlarge its finite generating set `X` to contain `S`, adding one relator per new letter. Linearity persists by the Theorem 2.34 sentence quoted in `osin-isolated-components-relative-area-citation`. Then pass to a reduced presentation. So each `x in S` is one `X`-letter, and `L_S = 1` below.

2. **Witnesses.** For `g in N \ {e}`, at most `|S|` pairs `(m, x)` satisfy `phi^-m(x) = g`, by step 1. So an edge `{u, v}` is present iff one of at most `2|S|` pairs, each with first coordinate `u` or `v`, is open.

3. **One path.** A self-avoiding path `(w_0, ..., w_l)` with edges in `{phi^-m(x)}` is open with probability at most `(2|S|)^l delta^(l/2)`.
   - Take a union bound over the choices of one open witness per edge.
   - A pair with first coordinate `w_i` witnesses only edges `i` and `i+1`, so a choice uses at least `l/2` distinct pairs.
   - These pairs are independent.

4. **Path count.** Write `w_j = g_j w_(j-1)` with `g_j = t^(-m_j) x_j t^(m_j)`. Then `s = g_l ... g_1` labels a cycle `q` of relative length at most `(L_S + 1)(l + 1)` in `Gamma(Gamma, X ∪ H)`. It uses the `H`-letters `t^(-m_l)`, `t^(m_j - m_(j-1))` and `t^(m_1)`, separated by fixed `X`-words for the `x_j` and for `s^-1`.
   - **Cosets.** Tracing vertices, the `H`-components lie in the cosets `s w_i^-1 H`, `i = 0, ..., l`. These are pairwise distinct, so every component is isolated.
   - **Exponent bound.** `osin-isolated-components-bounded-by-relative-area` bounds the sum of the `Omega`-lengths of the components by `M Area^rel(q) <= M (C l(q) + C')`. `Omega` is a finite subset of `H`, so `|t^d|_Omega >= |d| / max{|k| : t^k in Omega}`. Hence `|m_1| + sum_j |m_j - m_(j-1)| + |m_l| <= K (l+1)`.
   - **Count.** Counting integer vectors with bounded `l^1`-norm, together with the `|S|^l` choices of the `x_j`, gives at most `|S|^l 2^((K+2)(l+1))` paths.

5. **Two points.** `P(e <-> s) <= 2^(K+2) sum_(l>=1) (2^(K+3) |S|^2 sqrt(delta))^l`, which is `< 1` for small `delta`.

6. **Almost sure disconnection.** Right translation by `N` preserves the product law and maps `T_delta` to an isomorphic graph. The action of `N` on `N x Z` is free with infinite orbits, so the Bernoulli action is mixing, hence ergodic. So `P(T_delta connected) in {0, 1}`, and it is at most `P(e <-> s) < 1`, so it is `0`.
