---
rg: 2
id: amenable-kernel-ascent-from-positive-entropy-on-products
kind: route
title: Positive Rokhlin entropy for every amenable-by-INF group gives amenable-kernel ascent through the products P x W
target: rokhlin-maximality-ascends-amenable-normal-extensions
requires: [amenable-by-maximal-groups-have-positive-rokhlin-entropy, rokhlin-supremum-of-torsion-products-is-zero-or-infinite, seward-per-group-rokhlin-entropy-of-bernoulli-shifts]
---

## Why sufficient

Let `N ◁ W` be amenable, `q ≥ 2`, `|A| = q`. Suppose `h^Rok_(W/N)((A^k)^(W/N)) = k log q` for every `k ≥ 1`. We
show that `W` is Rokhlin-maximal at `q`. Write "item n" for item n of
`seward-per-group-rokhlin-entropy-of-bernoulli-shifts`.

**Case 1: `W/N` finite.** `W` is amenable, as an extension of the amenable group `N` by a finite group.
- If `W` is infinite, it is sofic, by the standard fact that amenable groups are sofic (Gromov; Weiss 2000), and
  item 4 gives `h^Rok_W((A^k)^W) = k log q`.
- If `W` is finite, the statement depends on the convention for non-ergodic actions.
  - With the plain infimum over generating partitions, the `W`-translates of a generating partition `α` generate
    the full algebra of `(A^k)^W`, whose entropy is `|W| k log q`. So `|W| H(α) ≥ |W| k log q`, and the time-zero
    partition attains the bound.
  - With Seward's convention `h_W(X) = inf H(α | I_W)` over partitions `α` with `σ-alg_W(α) ∨ I_W` generating,
    where `I_W` is the invariant σ-algebra, the hypothesis never holds for the finite group `Q = W/N`. If `Q` is
    trivial, `I_Q` is everything and the entropy is `0`. Otherwise the time-zero partition `α_0` is not
    independent of `I_Q`, since the invariant event "`x` is constant equal to `a`" forces `x(1) = a`. So
    `h_Q ≤ H(α_0 | I_Q) < H(α_0) = k log q`, and the implication is vacuous.

**Case 2: `W/N` infinite.**
1. **The quotient is INF.** Item 1 for the countably infinite group `W/N` gives
   `min(k log q, h_sup(W/N)) = k log q` for every `k`. So `h_sup(W/N) ≥ k log q` for all `k`, and INF(`W/N`).
2. **The product stays in the class.** Let `P = ⊕_(n ≥ 1) Z/nZ`, which is countable, abelian (hence amenable),
   and has the cyclic subgroups `Z/nZ` of unbounded order. `P × N` is normal in `P × W` and amenable, as a product
   of amenable groups. Moreover `(P × W)/(P × N) ≅ W/N` has infinite Rokhlin supremum.
3. **Apply the hole.** `amenable-by-maximal-groups-have-positive-rokhlin-entropy`, applied to `P × N ◁ P × W`,
   gives POS(`P × W`).
4. **Transfer to `W`.** `W` is countably infinite, since it surjects onto the infinite group `W/N`. By
   `rokhlin-supremum-of-torsion-products-is-zero-or-infinite` (item 3) with `G = W`, POS(`P × W`) implies INF(`W`).
5. **Conclude.** Item 1 for `W` gives `h^Rok_W((A^k)^W) = min(k log q, ∞) = k log q` for every `k`. ∎

**Remarks.**
- **Reverse direction.** The implication runs the other way too: the target gives INF(`W`), hence POS(`W`). So
  the hole is equivalent to the target, and this route is a reformulation. What it gains is that one free ergodic
  action with any positive Rokhlin entropy suffices, for the auxiliary group `P × W`.
- **Locally finite kernels.** `P` is locally finite, so the same argument with "amenable" replaced by "locally
  finite" reduces ascent across locally finite kernels to POS for locally-finite-by-INF groups. By
  `finite-kernel-ascent-from-amenable-kernel-ascent`, only that shape is needed for finite kernels.
- **Kun–Thom wreath.** For `W_KT`, maximality at every `q` is equivalent to POS(`P × W_KT`).
