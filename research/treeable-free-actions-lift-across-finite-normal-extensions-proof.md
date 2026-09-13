---
rg: 2
id: treeable-free-actions-lift-across-finite-normal-extensions-proof
kind: route
title: Lift the tautological cocycle along the edges of a treeing, then build the lift from the lifted cocycle
target: treeable-free-actions-lift-across-finite-normal-extensions
requires: []
---

Complete elementary proof. Notation: `1 -> N -> W -π-> Q -> 1` with `N` finite; `Q ↷ (Y, μ)` free p.m.p.;
`R = R_Y`; `c : R -> Q` the index cocycle, `c(y', y) = q` for the unique `q` with `q y = y'`. Freeness makes
`c` well defined and Borel off an invariant null set, which we discard throughout. Fix a Borel linear order `<`
on `Y` and a set-theoretic section `σ : Q -> W` of `π`.

## Step 1. The lifting criterion

**Lemma 1.** The following are equivalent.
1. There is a free p.m.p. `W`-space `(X, ν)` with a `π`-equivariant factor map `p : X -> Y` whose fibres are
   single `N`-orbits (the `N`-action on `X` is the restriction of the `W`-action).
2. There is a Borel `φ : Q × Y -> W` with `π(φ(q, y)) = q` and `φ(q_1 q_2, y) = φ(q_1, q_2 y) φ(q_2, y)`
   for all `q_1, q_2` and a.e. `y`.

*(2 ⇒ 1).* Setting `q_1 = q_2 = 1` gives `φ(1, y) = 1`. Put `X = Y × N`, `ν = μ × (uniform)`, and
`w·(y, n) = (π(w) y, w n φ(π(w), y)^-1)`.
- The second coordinate lies in `N`, since its image under `π` is `q · 1 · q^-1 = 1` with `q = π(w)`.
- Action. With `q_i = π(w_i)`:
  `w_1·(w_2·(y, n)) = (q_1 q_2 y, w_1 w_2 n φ(q_2, y)^-1 φ(q_1, q_2 y)^-1) = (q_1 q_2 y, w_1 w_2 n φ(q_1 q_2, y)^-1)`,
  which is `(w_1 w_2)·(y, n)`.
- Measure. For fixed `w`, `(y, n) -> (q y, w n φ(q, y)^-1)` is `y -> qy` on the base and a bijection of `N`
  on each fibre, so it preserves `ν`.
- `N` acts by `m·(y, n) = (y, m n)`, freely, with orbits the fibres of `p(y, n) = y`; `p` is `π`-equivariant.
- Freeness. If `w·(y, n) = (y, n)` then `π(w) y = y`, so `π(w) = 1` for a.e. `y`; then `w ∈ N` and `w n = n`,
  so `w = 1`.

*(1 ⇒ 2).* The fibres of `p` are finite, so there is a Borel section `s : Y -> X` of `p` (Lusin–Novikov). For
`w ∈ W`, the points `w·s(y)` and `s(π(w) y)` lie in the same fibre, which is one free `N`-orbit; so
`w·s(y) = β(w, y)·s(π(w) y)` for a unique Borel `β(w, y) ∈ N`. Writing `q_2 = π(w_2)`,
`w_1 w_2·s(y) = (w_1 β(w_2, y) w_1^-1) w_1·s(q_2 y) = (w_1 β(w_2, y) w_1^-1) β(w_1, q_2 y)·s(q_1 q_2 y)`,
so `β(w_1 w_2, y) = w_1 β(w_2, y) w_1^-1 · β(w_1, q_2 y)`. Put `φ'(w, y) = β(w, y)^-1 w`. Then
`φ'(w_1 w_2, y) = β(w_1, q_2 y)^-1 w_1 β(w_2, y)^-1 w_1^-1 w_1 w_2 = φ'(w_1, q_2 y) φ'(w_2, y)`.
For `n ∈ N`, `n·s(y) = β(n, y)·s(y)` forces `β(n, y) = n`, so `φ'(n, y) = 1` and `φ'(w n, y) = φ'(w, y)`.
Hence `φ(q, y) := φ'(w, y)` for any `w ∈ π^-1(q)` is well defined, satisfies the cocycle identity, and
`π(φ(q, y)) = π(β^-1) π(w) = q`. ∎

## Step 2. Lifting the index cocycle on a treeing

Let `G ⊂ R` be a treeing: a Borel symmetric irreflexive graph on `Y` whose connected components are the
`R`-classes and are trees, a.e.

*Edge labels.* For an edge `(y', y) ∈ G` put `e(y', y) = σ(c(y', y))` if `y < y'`, and
`e(y', y) = e(y, y')^-1` if `y' < y`. Then `e(y, y') e(y', y) = 1` and `π(e(y', y)) = c(y', y)`, because `c` is a
cocycle and `c(y, y') = c(y', y)^-1`.

*Path products.* For `(y', y) ∈ R` let `y = y_0, y_1, ..., y_k = y'` be the unique path without backtracking
from `y` to `y'` in the tree, and put `Φ(y', y) = e(y_k, y_(k-1)) ⋯ e(y_1, y_0)` (and `Φ(y, y) = 1`).
- Borel: `R` is the disjoint union of the Borel sets `R_k` of pairs at tree distance `k`, and on `R_k` the
  intermediate vertices are Borel functions of `(y', y)` by Lusin–Novikov uniformization, since `G` has
  countable sections.
- Multiplicative: for `(y'', y'), (y', y) ∈ R`, concatenate the two geodesics. In a tree the concatenation
  reduces to the geodesic from `y` to `y''` by deleting backtracks `a -> b -> a`. Each deletion removes a factor
  `e(a, b) e(b, a) = 1`. So `Φ(y'', y) = Φ(y'', y') Φ(y', y)`.
- Lifts `c`: `π(Φ(y', y)) = c(y_k, y_(k-1)) ⋯ c(y_1, y_0) = c(y', y)`.

## Step 3. Conclusion

Put `φ(q, y) = Φ(q y, y)`. Then `π(φ(q, y)) = c(q y, y) = q`, and
`φ(q_1 q_2, y) = Φ(q_1 q_2 y, q_2 y) Φ(q_2 y, y) = φ(q_1, q_2 y) φ(q_2, y)`. Lemma 1 (2 ⇒ 1) gives the lift. ∎

## The consequences stated in the claim

- **Extensions.** If `p : Z -> Y` is a factor map of free `Q`-actions and `φ` lifts `Y`, then `φ(q, p(z))`
  satisfies Lemma 1(2) on `Z`, because `p(q z) = q p(z)`.
- **Positive polarity.** If `Y` is free, treeable and `Y ≺ [0,1]^Q`, then `Y` lifts by Steps 1-3, and
  `[0,1]^Q ≺ Y` by `abert-weiss-free-actions-weakly-contain-bernoulli`, so `Y` is weakly equivalent to Bernoulli.
- **Non-treeability from rigidity.** If `[0,1]^Q` were treeable over a w-rigid `Q`, it would lift across every
  finite extension, and `bernoulli-lifts-across-finite-kernels-force-virtual-splitting` would make every finite
  extension of `Q` virtually split. For a w-rigid `Q` with a non-virtually-split finite extension (Deligne's
  `E_3 -> Sp_4(Z)`, not virtually split by `finite-central-extension-rf-iff-virtually-splits`) this is false.
- **Amalgams.** Over `A *_C B` the restrictions of `R_Y` to `A` and `B` carry lifts `φ_A`, `φ_B` whenever those
  subrelations are treeable. For central `N`, `θ = φ_A φ_B^-1` on `C × Y` is an `N`-valued cocycle. The action
  lifts exactly when `θ` is cohomologous to `α|_C · β|_C^-1` for cocycles `α` of `A ⋉ Y` and `β` of `B ⋉ Y`,
  because a lift restricts to `A` and `B` and two lifts on one subgroupoid differ by an `N`-valued cocycle.
