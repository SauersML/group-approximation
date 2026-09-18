---
rg: 2
id: toms-swap-drop-locus-codimension-proof
kind: route
title: Double the arc to a closed manifold, use Alexander duality to extend the support bundle's Chern classes over a small drop set, and count roots as in the constant-rank case
target: toms-swap-drop-locus-has-codimension-at-most-2m-plus-1
requires: []
---

Notation is from the target. Cohomology is singular with rational coefficients.
`u in H^2(CP^j)` is the hyperplane class.

**Step 0 (m <= j).** Since `dim D >= -1`, the hypothesis gives `2m <= 2j`.

**Step 1 (doubling).** Identify `Z` with `[0,1]` and glue two copies of `[0,1]`
along their endpoints to get `S^1`, with the reflection `ρ` exchanging the copies.
Put `M = S^1 x CP^j`, a closed oriented manifold of dimension `n = 2j + 1`, and
`Q~ = Q ∘ (fold x id)`. This is continuous, with the same maximal rank `m`, and
drop set `D~ = D ∪ ρD`. A union of two closed sets of dimension `<= d` has
dimension `<= d`, so `dim D~ = dim D`.

**Step 2 (support bundle).** On the open set `U = M \ D~` the rank of `Q~` is `m`.
Near each point the `m` largest eigenvalues are bounded away from `0`, and the
others vanish. So the spectral projection `E(w) = 1_(0,∞)(Q~(w))` is given locally
by a holomorphic functional calculus with a fixed contour, and it is continuous
on `U`. Call its range bundle `E`, of rank `m`.

**Step 3 (Alexander duality).** For compact `D~` in the oriented `n`-manifold `M`,
`H_q(M, U) ≅ Ȟ^(n-q)(D~)` (Čech cohomology; Dold, *Lectures on Algebraic Topology*,
Ch. VIII, Sec. 7). Čech cohomology vanishes above the covering dimension, so
`H_q(M, U) = 0` for `q < n - dim D~`. Over a field, `H^q(M, U) = Hom(H_q(M, U), Q)`
also vanishes there. The exact sequence `H^q(M) -> H^q(U) -> H^(q+1)(M, U)` shows
that `H^q(M) -> H^q(U)` is onto for `q <= n - dim D - 2 = 2j - 1 - dim D`. The
hypothesis `dim D <= 2j - 2m - 1` gives this for every `q <= 2m`. By Künneth,
`H^(2k)(M) = Q u^k` for `2k <= 2j`. So there are rationals `n_k` with

```text
c_k(E) = n_k u^k |_U     for 0 <= k <= m,   n_0 = 1.
```

Put `N(u) = sum_(k <= m) n_k u^k in Q[u]`.

**Step 4 (slices).** Let `Y_i = {z_i} x CP^j` and `D_i = D ∩ Y_i`. Then
`dim D_i <= dim D <= 2j - 2m - 1`. The same duality in `CP^j` (dimension `2j`)
gives `H^q(CP^j, CP^j \ D_i) = 0` for `q < 2j - dim D_i`, in particular for all
`q <= 2m`. So `H^(2k)(CP^j) -> H^(2k)(CP^j \ D_i)` is injective for `k <= m`, and
`u^k` restricts to a nonzero class for `k <= m`.

**Step 5 (sub-bundle).** Restriction is a `*`-homomorphism, so `e_i <~ Q_i := Q|Y_i`.
For a projection `e` and a positive `b` with `e <~ b`, there are `delta > 0` and `x`
with `e = x (b - delta)_+ x^*`. Then `v = (b - delta)_+^(1/2) x^*` has `v^* v = e`, and
`vv^*` is a projection in the hereditary subalgebra of `(b - delta)_+`. At every point,
the range of `vv^*` lies in the range of `1_(delta,∞)(b)`, which is contained in the
support of `b`. Apply this with `b = Q_i`. Over `CP^j \ D_i` the support of `Q_i` is
`E`, so `F_i := range(vv^*) ≅ range(e_i) = L_1^(p_i) ⊕ L_2^(q_i) ⊕ θ^(π_i)` is a
sub-bundle of `E|(CP^j \ D_i)`. Let `S_i` be its orthogonal complement in `E`. It has
rank `s_i = m - p_i - q_i - π_i`, so `s_i >= 0`.

**Step 6 (Chern count).** On `CP^j \ D_i`, `c(E) = c(F_i) c(S_i)`, with
`c(F_i) = (1 + alpha u)^(p_i) (1 + beta u)^(q_i)`. This is a unipotent polynomial in
`u`, invertible in `Q[[u]]`. Let `G_i(u) = N(u) c(F_i)^(-1) mod u^(m+1)`. Solving
`c(S_i) = c(E) c(F_i)^(-1)` degree by degree gives `c_k(S_i) = [u^k] G_i · u^k|` for
`k <= m`. Now `c_k(S_i) = 0` for `k > s_i`, and `u^k|` is nonzero for `k <= m` by Step 4.
So `[u^k] G_i = 0` for `s_i < k <= m`, and `G_i = g_i` is a polynomial of degree
`<= s_i`. Hence

```text
N(u) ≡ (1 + alpha u)^(p_i) (1 + beta u)^(q_i) g_i(u)   mod u^(m+1),   i = 0, 1.
```

The right side has degree `<= p_i + q_i + s_i = m - π_i <= m`, so both are equalities
in `Q[u]`, and

```text
(1 + alpha u)^(p_0) (1 + beta u)^(q_0) g_0  =  N  =  (1 + alpha u)^(p_1) (1 + beta u)^(q_1) g_1.
```

Let `nu_i` be the multiplicity of the root `-1/beta` in `g_i`, so `0 <= nu_i <= s_i`.
Since `alpha != beta`, `1 + alpha u` does not vanish there. So `q_0 + nu_0 = q_1 + nu_1`,
and `q_0 - q_1 = nu_1 - nu_0 in [-s_0, s_1]`. If `alpha != 0`, the root `-1/alpha`
gives the same for `p`. This proves the theorem.

**Step 7 (swap corollary).** Let `c > 0` be below the positive spectra of `B_x`, `B_y`
and `Π`. Then `e_0 = supp B_x tensor gamma_1 + supp B_y tensor gamma_2 + supp Π` is at most
`c^(-1)` times the contained element, so `e_0 <~ Q|Y_0`, with
`(p_0, q_0, π_0) = (R_x, R_y, π)`. Likewise `(p_1, q_1, π_1) = (R_y, R_x, π)`. Suppose
`dim D <= 2j - 2m - 1`. The theorem gives `R_y - R_x <= s_1 = m - R_x - R_y - π`, so
`m >= 2R_y + π`, and `R_y - R_x >= -s_0` gives `m >= 2R_x + π`. This contradicts
`m < 2 max(R_x, R_y) + π`. So `dim D >= 2j - 2m`.

**Step 8 (consequence in A).** Follow Step 7 of
`toms-constant-rank-twisted-transport-proof`, with `Q = a_(n+1)` at stage `M` on
`K = Z x CP^j`. `Z` is an arc from `(x(0), x(1))` to `(x(1), x(0))`, because `c` is
embedded.
- *Upper band.* It gives `m <= r_(M-1)`.
- *Contained elements.* `phi_(M-1)(a')` with `a' = phi_(N_n, M-1)((a_n - eps)_+)`
  satisfies `phi_(M-1)(a') <~ a_(n+1)`, and restriction to a slice preserves `<~`.
  Its slices at the two endpoints are `a'(x) tensor gamma_1 + a'(y) tensor gamma_2`,
  with `(x, y) = (x(0), x(1))` and `(x(1), x(0))`, and `π = 0`.
- *Rank.* `R_y = rank a'(x(1)) > r_(M-1)/2`, so `2 max(R_x, R_y) > r_(M-1) >= m`.

Step 7 gives `dim D >= 2j - 2m >= 2j - 2 r_(M-1)`. Square.
