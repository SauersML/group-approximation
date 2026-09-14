---
rg: 2
id: stable-vertex-mf-trace-models-need-inequivalent-marginals-proof
kind: route
title: A Kazhdan near-identity intertwiner completes to a unitary and gives an exact model with the same traces
target: stable-vertex-mf-trace-models-need-inequivalent-marginals
requires: []
---

## Direct proof

Fix a Kazhdan pair `(F, epsilon)` for `Gamma`.  In every unitary representation,
`||xi - P xi|| <= epsilon^(-1) max_(s in F) ||rho(s) xi - xi||`, where `P`
projects onto the invariant vectors.  Norms `|| ||_2` are normalized
Hilbert--Schmidt norms.

**1. Near-identity intertwiner.**  Put
`delta_n = max_(s in F) ||pi^2_n(s) - pi^1_n(s)||_op`.  Since
`iota_1(s) = iota_2(s)` in `D`, the hypotheses give `delta_n -> 0`.  Let `Gamma`
act on `M_(d_n)` by `rho(g)X = pi^2(g) X pi^1(g)*`, unitary for `|| ||_2`.  Then
`||rho(s)1 - 1||_2 <= delta_n`, so there is an intertwiner `X`,
`pi^2(g) X = X pi^1(g)` for all `g in Gamma`, with `||X - 1||_2 <= delta_n/epsilon`.

**2. Completion.**  Assume `pi^1|_Gamma ~= pi^2|_Gamma`.  Write `X = V|X|`.
The polar part `V` intertwines, and `e = V*V`, `f = VV*` commute with the
respective images.  Finite-dimensional representations cancel, so the
complements `(1-e)` and `(1-f)` carry equivalent subrepresentations.  Choose a
unitary intertwiner `V'` between them and put `U = V + V'`, a unitary with
`pi^2(g) U = U pi^1(g)` on `Gamma`.  The kernel of `X` lies in the range of
`1-e`, and every unit vector there has `||(1-X) xi|| = 1`, so
`tr(1-e) <= ||1-X||_2^2`.  By the Araki--Yamagami inequality,
`||1-|X| ||_2 <= sqrt(2) ||1-X||_2`.  Hence

```text
||U - 1||_2 <= ||V(1-|X|)||_2 + ||X-1||_2 + ||V'||_2 <= (2 + sqrt 2) delta_n / epsilon.
```

**3. Exact model.**  `tau_n(iota_1(g)) = U pi^1(g) U*` and
`tau_n(iota_2(g)) = pi^2(g)` agree on `Gamma`, so they define a genuine
representation of `D`.  For a fixed word `w = g_1 h_1 ... g_l h_l`,
`sigma_n(w)` is within `o(1)` in operator norm of
`pi^1(g_1) pi^2(h_1) ...`, and `tau_n(w)` is within
`2 l ||U - 1||_2` of the same product in `|| ||_2`.  Normalized traces are
`|| ||_2`-Lipschitz on contractions, so `tr(tau_n(w)) -> delta_e(w)` along every
subsequence where step 2 applies.

**4. Contradiction.**  If equivalence held for infinitely many `n`, then for
each `g != e` some genuine finite-dimensional representation `tau_n` has
`tr(tau_n(g))` near `0`, hence `tau_n(g) != 1`.  So `D` would be maximally
almost periodic.

**Permutation corollary.**  Two distinct permutation matrices are at operator
distance at least `sqrt(2)`.  So `delta_n < sqrt(2)` forces `pi^1 = pi^2` on a
finite generating set of `Gamma`, hence on `Gamma`.  Then step 3 applies with
`U = 1`, and step 4 gives the contradiction.
