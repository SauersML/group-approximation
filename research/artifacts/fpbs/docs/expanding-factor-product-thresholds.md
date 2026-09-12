# Strict thresholds on Cartesian products with a strongly expanding factor

Lane `bs-p2to2-product-graphs`, 2026-09-12. Target: `p_c < p_{2->2}` on Cayley
graphs of `Gamma x Z` with `Gamma` a surface group, for a natural class of
generating sets not covered by nonunimodularity. This note proves it for the
product generating sets of `Gamma_g x Z^k` built from the standard surface
generators, whenever `g >= 3` and `1 <= k <= g-2` (and `k = 1` for `g = 3`).
The method is perturbative: an explicit upper bound on `p_c` against the
walk-counting lower bound on `p_{2->2}`. It does not reach genus two, mixed
generating sets, or nontrivial Seifert bundles. Nothing here is refereed or
formalized, and no novelty is claimed for the method.

## 0. Setting and inputs

`G = Cay(H, S_H)` is `d`-regular, `K = Cay(L, S_L)` is `d_K`-regular, and
`X = G □ K = Cay(H x L, (S_H x {1}) ∪ ({1} x S_L))`. Edge expansion is
`h(Y) = inf{ |∂_E F| / |F| : F ⊂ V(Y) finite nonempty }`. `A_Y` is the
adjacency operator on `l2(V(Y))`, and `T_p` has kernel `tau_p(x,y)`.

* **(E1) Exploration bound.** Every infinite connected locally finite graph
  with edge expansion at least `h > 0` has `p_c <= 1/(1+h)`
  (`fpbs-expansion-thinning-threshold`; Benjamini–Schramm 1996 give the same
  bound).
* **(E2) Walk counting.** `tau_p(x,y) <= sum_l p^l A^l(x,y)`, so
  `p ||A_Y|| < 1` gives `||T_p|| <= (1 - p||A_Y||)^(-1)` and
  `p_{2->2}(Y) >= 1/||A_Y||`. This is step 3 of
  `fpbs-tree-projected-large-rank-proof`.
* **(E3) `p_{2->2} <= p_u`.** Above `p_u`, `tau_p >= theta(p)^2 > 0` and `T_p` is
  unbounded (step 4 of the same proof; Hutchcroft arXiv:1804.10191, Section 2).
* **(E4) Spectral Cheeger bound (Mohar).** For a `d`-regular graph with edge
  expansion `h`, `||A|| <= sqrt(d^2 - h^2)`. This is Lyons–Peres, *Probability on
  Trees and Networks*, Theorem 6.7 (`1 - rho >= 1 - sqrt(1 - Phi_E^2)`, with
  `rho = ||P||` and `Phi_E(G;1;deg) = h/d`), which the book credits to an
  improvement due to Mohar. It was read from the book PDF on MSI and is imported
  as `fpbs-mohar-adjacency-norm-cheeger-bound`.
* **(E5) Tiling constants (Häggström–Jonasson–Lyons).** A planar regular graph
  `G` with regular dual `G†` has
  `inf |∂_E K|/|K| = (d_G - 2) sqrt(1 - 4/((d_G - 2)(d_(G†) - 2)))`.
  This is arXiv:math/0008191v2, Theorem 4.1 with Remark 4.2 (such `G` is
  transitive), plus the identity `ι'_E = ι_E` for transitive graphs quoted there
  from Benjamini–Lyons–Peres–Schramm. It was read from the PDF text on MSI and is
  imported as `fpbs-regular-tiling-edge-isoperimetric-constant`.
* **(E6) Surface group Cayley graph.** For
  `Gamma_g = <a_1,b_1,...,a_g,b_g | [a_1,b_1]...[a_g,b_g]>`, `g >= 2`, the Cayley
  graph for `{a_i^(±1), b_i^(±1)}` is the 1-skeleton of the regular tiling of
  the hyperbolic plane by `4g`-gons with `4g` meeting at each vertex (Poincaré's
  polygon theorem). Standard, not re-read here.

## 1. The product criterion

**Theorem 1.** If `1 + h(G) > ||A_G|| + d_K`, then on `X = G □ K`

    p_c(X)  <=  1/(1+h(G))  <  1/||A_X||  <=  p_{2->2}(X)  <=  p_u(X),

so `p_c(X) < p_{2->2}(X)` and `p_c(X) < p_u(X)`.

*Proof.*
1. `G x {1}` is a subgraph of `X`, so `p_c(X) <= p_c(G) <= 1/(1+h(G))` by (E1).
2. `A_X = A_G ⊗ I + I ⊗ A_K`, and `||A_K|| <= d_K` for a `d_K`-regular graph. By
   the triangle inequality `||A_X|| <= ||A_G|| + d_K < 1 + h(G)`.
3. So `1/(1+h(G)) < 1/||A_X||`, and (E2), (E3) finish. QED.

**Corollary 2.** If `1 + h > sqrt(d^2 - h^2) + d_K` with `h = h(G)`, the
conclusion of Theorem 1 holds. *Proof:* (E4) in Theorem 1.

**Remarks.**
* `K` is arbitrary. Only its degree enters, so the criterion also covers
  `G □ Cay(L, S_L)` for nonamenable `L`, where `||A_K|| < d_K` would give more.
* The amenable kernel `{1} x L` gives equality in the fibre comparison
  (`fpbs-fibre-summed-connectivity-operator`). So on these graphs the critical
  fibre operator over `H` is bounded, and the one-radius condition of
  `fpbs-critical-sphere-fibre-operator-below-one` holds at that graph by
  `fpbs-sphere-fibre-operator-iff-critical-fibre-l2`.
* **Sketch, not used and not checked.** A column decomposition would improve the
  condition. Split a self-avoiding path in `G □ Z` into maximal vertical runs
  (monotone, weight `p/(1-p)` per run and direction) and horizontal layer
  segments (nonempty between runs). BK then gives
  `sigma_p <= tau + sum_r R^r tau*(tau-delta)^(*(r-1))*tau`, with `R = 2p/(1-p)`
  and `tau` the layer two-point function. With `N(tau - delta) = N(tau) - 1`
  (positive kernels) and walk counting on the layer, the condition `x + 2p < 1`,
  `x = p||A_G||`, becomes `x + p + px < 1`. It changes none of the genus
  thresholds below.

## 2. Surface groups times free abelian groups

**Corollary 3.** Let `g >= 2`, `k >= 1`, and let `X_(g,k)` be the Cayley graph of
`Gamma_g x Z^k` for the product generating set
`{(a_i^(±1),0), (b_i^(±1),0), (1, ±e_j)}`. If

    2k  <  1 + sqrt((4g-2)^2 - 4) - 4 sqrt(g),                    (2.1)

then `p_c(X_(g,k)) < p_{2->2}(X_(g,k)) <= p_u(X_(g,k))`. Condition (2.1) holds
whenever `g >= 3` and `1 <= k <= max(1, g-2)`. It fails for every `k >= 1` at
`g = 2`.

*Proof.*
1. By (E6), `G = Cay(Gamma_g, standard)` is the `{4g,4g}` tiling graph, with
   `d = 4g`. By (E5) with `p = q = 4g`,
   `h(G) = (4g-2) sqrt(1 - 4/(4g-2)^2) = sqrt((4g-2)^2 - 4)`.
2. Then `d^2 - h^2 = 16g^2 - (16g^2 - 16g) = 16g`, so (E4) gives
   `||A_G|| <= 4 sqrt(g)`.
3. `K = Cay(Z^k, {±e_j})` has `d_K = 2k`. Corollary 2 applies under (2.1).
4. **Range.** For `g >= 2`, `(4g-2)^2 - 4 >= (4g-3)^2` because `8g >= 9`. So the
   right side of (2.1) is at least `4g - 2 - 4 sqrt(g)`.
   * `k <= g-2`: `2(g-2) < 4g - 2 - 4 sqrt(g)` is `2 sqrt(g) < g+1`, i.e.
     `(sqrt(g)-1)^2 > 0`, true for `g >= 2`.
   * `g = 3, k = 1`: the right side of (2.1) is `1 + sqrt(96) - 4 sqrt(3)
     = 3.870... > 2`.
5. **Genus two.** The right side of (2.1) is `1 + sqrt(32) - 4 sqrt(2) = 1 < 2k`.
   QED.

**Table of (2.1).** The right side is `R(g) = 1 + sqrt((4g-2)^2-4) - 4 sqrt(g)`.

| `g` | `R(g)` | largest `k` |
|---|---|---|
| 2 | 1.000 | none |
| 3 | 3.870 | 1 |
| 4 | 6.856 | 3 |
| 5 | 9.944 | 4 |
| 6 | 13.111 | 6 |

## 3. Why this class is not covered by nonunimodularity

For the tree factor (`F_n` with a free basis) the product graph carries a
closed nonunimodular quasi-transitive group of automorphisms, and Hutchcroft's
theorem applies (`fpbs-hyperbolic-and-nonunimodular-nonuniqueness`; Attempts of
`fpbs-product-every-generating-set`). The `{4g,4g}` tiling graph has a discrete
automorphism group acting cocompactly on the hyperbolic plane, which is
unimodular. If `Aut(G □ Z^k)` is generated by factor automorphisms and
coordinate permutations of the `Z` factors (unique prime factorization of
connected Cartesian products, Imrich; not re-read here), it is discrete, so
unimodular, and Hutchcroft's nonunimodular theorem does not apply. Treat this
section as orientation. The theorem above does not use it.

The graphs `X_(g,k)` also fall outside the other class theorems:
* `Gamma_g x Z^k` has infinite centre, so it is not acylindrically hyperbolic
  (Choi–Seo);
* it has fixed price one, so Lyons's cost criterion is silent.

## 4. Where it stops

* **Genus two.** (2.1) fails. Better inputs do not close it either: with
  `rho(Gamma_2) <= 0.6629` (Nagnibeda, not re-read), `||A_G|| <= 5.303`, walk
  counting needs `p_c(X) < 1/7.303 = 0.1369`. The available upper bounds are
  `1/(1+h) = 0.1502` and the geodesic-tree bound `1/gr ≈ 0.1433`. The growth rate
  `gr(Gamma_2) ≈ 6.98` (Cannon) is recalled, not re-read, so treat these numbers
  as orientation.
* **Mixed generating sets.** Generators with nontrivial components in both
  factors make `X` non-Cartesian (`fpbs-mixed-gen-set-not-cartesian`), and the
  subgraph step 1 of Theorem 1 no longer isolates an expanding copy of `G`.
* **Nontrivial Seifert bundles.** Central extensions of Fuchsian groups have no
  product generating set, so `fpbs-seifert-fibred-every-generating-set` is
  touched only at trivial bundles `S_g x S^1`, `g >= 3`.
* **Every generating set.** The proof is perturbative in the degree of the
  expanding factor. It gives no information on small generating sets, which is
  where Choi–Seo Questions 1.3 and 1.6 are hard.

## 5. Trust surfaces

* (E4) and (E5) are imported from their sources, checked on MSI as recorded in
  the citation routes.
* (E6) and the factorization remark are standard and were not re-read.
* (E1), (E2) and (E3) are established on main.
