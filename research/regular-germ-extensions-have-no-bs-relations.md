---
rg: 2
id: regular-germ-extensions-have-no-bs-relations
kind: claim
title: No regular finite germ extension of V contains an infinite-order element conjugate to a proper power of itself
distinct_from:
  regular-germ-extension-attractors-are-undistorted: that is the established part, which proves this for elements with an attracting or repelling periodic point or with a non-trivial wandering singular germ; this is the full statement, open for the remaining dynamical type.
  normal-germ-extensions-of-thompson-v-contain-no-sl3z: that excludes finite-index subgroups of SL_3(Z) and shows BS(1,2) cannot map with a of infinite order into the germ groups; this asks whether BS(1,k) embeds in the group G itself.
  gl-n-q-embeds-in-fp-simple-group: that is the embedding question; this would exclude the case n = 2, and Aff(Q) and SL_2(Q), from one whole family of candidate hosts.
---

**OPEN.** Let `G` be a finite germ extension of Thompson's group `V` that is
**regular** in the sense of `regular-germ-extension-attractors-are-undistorted`,
that is (E) + (H3) + (T) at every singular point. Then there are no `a, t ∈ G`
with `a` of infinite order and `t a t^-1 = a^k` for some `|k| >= 2`.

**Why it matters.** `Aff(Q) <= GL_2(Q)` contains `BS(1,2)`, and `SL_2(Q)` contains
`BS(1,4)`. So this claim would exclude `GL_2(Q)`, `SL_2(Q)` and `Aff(Q)` from every
regular germ extension. Regular means the Belk–Hyde–Matucci Corollary 2.10 regime
together with (T). For `n >= 3`, `normal-germ-extensions-of-thompson-v-contain-no-sl3z`
already excludes that regime. `VA` is regular, and for it the claim holds
(Burillo–Felipe; root obstruction O4).

## Attempts

1. **Two length functions (gq-va-gl2, 2026-09-17), partial.** By
   `regular-germ-extension-attractors-are-undistorted`, the claim holds for every
   `a` that has an attracting or repelling periodic point, or a wandering singular
   orbit whose total germ is not a `V`-germ. The singularity count `s` and the
   depth-gain Lipschitz constant `Lip` grow linearly along such `a`, and at most
   logarithmically along `a^(k^j) = t^j a t^-j`.

   **Left:** elements `a` with no attracting or repelling periodic point, with
   trivial total germs on wandering singular orbits, and whose singular points lie
   in finite orbits. At such a point `p`, the germ `α` of `a^q` centralizes a
   contracting germ `σ_p`.

2. **Such germs exist and defeat both length functions.** Take `p = 0^∞`,
   `σ(y) = 0y`, levels `0^m 1 C`, and define `α` by
   - `0^m 10 z -> 0^(m-1) 100 z`,
   - `0^m 110 z -> 0^m 101 z`,
   - `0^m 111 z -> 0^(m+1) 11 z`.

   Each target level `0^j 1 C` is hit exactly once, by `100` from level `j+1`, by
   `101` from level `j` and by `11` from level `j-1`. So `α` is a
   `σ`-equivariant bijection near `p`, and every piece has depth gain `0`.

   It has infinite order: `α^n(0^m 10 z) = 0^(m-n) 1 0^(n+1) z` for `n <= m`.
   Completing it by prefix replacements outside `cone(00)` gives `h ∈ Homeo(C)` with
   `sing(h) = {p}` and `h(p) = p`.

   *Sketch, not checked in detail:* `G = <V, h>` is regular, and `(G)_p = <α, τ_p>`
   is abelian. Here `Lip(α^n) = 0` and `s(h^n) = 1` for all `n`, so neither length
   function sees `α`.

   The induced map on the annulus `1C`, namely `10 z -> 100 z`, `110 z -> 101 z`,
   `111 z -> 11 z`, is an infinite-order element of `V(1C)`. The level drift
   exactly balances its contraction.

   **Open test:** is such an `h`, or a product of such elements with `V`, ever
   conjugate in a regular `G` to a proper power of itself? The order structure that
   Burillo–Felipe use for `VA` is absent here. A proof would need a third invariant,
   for example an asymptotic level-drift rate along orbits of the annulus map.
