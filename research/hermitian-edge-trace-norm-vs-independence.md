---
rg: 2
id: hermitian-edge-trace-norm-vs-independence
kind: claim
title: A Hermitian matrix supported on the edges of a graph, with entries of modulus at least 1, has weighted trace norm at least sqrt3 (W - alpha_w)
artifacts:
  - experiments/qudit-weyl-rounding-multiqudit-2026-09-18/README.md
distinct_from:
  qudit-weyl-rounding-one-qudit-constant-is-2d-over-sqrt3-pi: that proves the Weyl-specific one-qudit case (complete multipartite graphs coming from lines of F_d^2) with Turán's theorem; this is the general matrix inequality for every graph and every complex phase pattern.
---

**OPEN (conjecture; tight at the triangle; numerics).** Let `G` be a finite graph on `[N]`, let
`w in R_{>=0}^N`, and put `W = sum w_i`, `alpha_w = max` of `w(I)` over independent sets `I` of `G`,
and `D = diag(sqrt w)`. Let `C` be a Hermitian matrix with `C_ii = 0`, `C_ij = 0` for non-edges, and
`|C_ij| >= 1` for edges. The conjecture is

```text
(**)     || D C D ||_1  >=  sqrt3 ( W - alpha_w(G) ) .
```

**Equivalent form (STAB membership).** `||DCD||_1 = min { sum_i w_i Q_ii : Q >= C, Q >= -C }`. So
(**) for all `w` says the following. For every such `C` and every Hermitian `Q` with `Q +- C >= 0`,
the vector `y_i = (1 - Q_ii/sqrt3)_+` lies in the stable-set polytope `STAB(G)`. Equivalently,
there is a random independent set `I` with `Pr(i in I) >= y_i`.

**Why it matters.** By `qudit-weyl-rounding-constant-2d-over-sqrt3-pi-via-trace-norm`, (**) implies
that the Weyl stabilizer rounding constant on any number of prime-`d` qudits is at most
`2d/(sqrt3 pi) + 4 + O(1/d)`. With `qudit-weyl-rounding-constant-triangular-harper-bound`, it would
settle `c_d = 2d/(sqrt3 pi) + O(1)`.

**Known cases.**
- **Triangle, all weights (tight).** `tr DCD = 0`, so `||DCD||_1 >= sqrt2 ||DCD||_F
  >= 2 (w_1w_2 + w_1w_3 + w_2w_3)^(1/2)`. Take `w_3` maximal and `a = w_1 <= b = w_2`. Then
  `4(ab + (a+b)w_3) - 3(a+b)^2 >= 4(2ab + b^2) - 3(a+b)^2 = (b-a)(b+3a) >= 0`, which is (**).
  Equality holds at `w = (1,1,1)/3`, `|C_ij| = 1`, flux `arg(C_12 C_23 C_31) = pi/2`. The
  eigenvalues are then `+-sqrt3, 0`.
- **Bipartite graphs.** The `2x2` minors of `Q + C >= 0` and `Q - C >= 0` give
  `Q_ii Q_jj >= max |Q_ij +- C_ij|^2 >= |C_ij|^2 >= 1` on every edge. So if `y_i, y_j > 0` then
  `y_i + y_j <= 2 - 2/sqrt3 < 1`. Edge constraints cut out STAB for bipartite graphs. More generally,
  for perfect graphs (**) reduces to the clique facets.
- **Disjoint unions.** Both sides are additive.
- **Weyl one-qudit case.** Here `G` is complete multipartite and `C` is the commutator matrix of Lemma L
  in `qudit-weyl-rounding-one-qudit-constant-is-2d-over-sqrt3-pi-proof`. This case is proved there,
  with constant `sqrt3 (1 - O(1/d))`, by Frobenius plus Turán.

**Numerics** (`experiments/qudit-weyl-rounding-multiqudit-2026-09-18/`).
- `complex_star.py`: local minimization over phases, moduli `>= 1` and weights, on random graphs
  with `N = 5, 6` and `p = 0.5, 0.7`, and on `K_3, K_4, K_5`. The minimum ratio
  `||DCD||_1 / (sqrt3 (W - alpha_w))` was never below `1`. It equals `1.000000` whenever the search
  reaches a triangle with weights `1/3`.
- `clique_uniform.py`: for `K_m` with uniform weights, the minimum of `||C||_1/(sqrt3 (m-1))` is
  `1.000, 1.053, 1.045, 1.072, 1.093, 1.093` for `m = 3, ..., 8`.
- `graph_relaxed.py` (purely imaginary `C = i Omega`, the semiclassical Weyl regime, by an SDP in `Q`
  alternating with an LP in `w`): the minimum ratio is `sqrt3` to solver tolerance for
  `N = 6, 7` and `p = 0.4, 0.6, 0.8`, again at a triangle.
- Odd cycles with uniform weights: `min ||C||_1 = 6.155, 8.763, 11.343, 13.910` for
  `C_5, C_7, C_9, C_11`, against the required `5.196, 6.928, 8.660, 10.392`.

## Attempts

1. *Frobenius only* (as in the one-qudit proof and the triangle case). `tr C = 0` gives
   `||C||_1 >= sqrt2 ||C||_F >= sqrt(2m(m-1))` on `K_m`. This proves (**) for `K_m` with uniform
   weights only for `m <= 3`. It dies at `m = 4`, because `sqrt24 = 4.90 < 3 sqrt3 = 5.20`. On one qudit,
   Weyl structure rescues it: Lemma T forces many pairs with `|1 - omega^t| >= 2 sin(2pi/d)`. In general
   `C` has no such structure, so a genuine trace-norm (non-Frobenius) argument is needed for large
   cliques.
2. *Edge minors only.* `Q_ii Q_jj >= 1` on edges gives `y_i + y_j <= 2 - 2/sqrt3 = 0.845`. On `C_5`
   this allows `sum y` up to `5 x 0.4226 = 2.11 > 2 = alpha`. So it dies at the first odd cycle. The
   odd-cycle facets need the full `5x5` condition, which holds with room to spare (numerics above).
   A proof must use principal submatrices of size at least `3` (triangles) and odd-cycle structure
   together.
3. *Deferred*: a rounding proof via the Gram vectors of `Q + C` and `Q - C`. These are vectors
   `a_i, b_i` with `|a_i| = |b_i| = sqrt(Q_ii)`, equal inner products on non-edges, and
   `|<a_i,a_j> - <b_i,b_j>| >= 2` on edges. It would produce the random independent set directly.
   This mirrors the quantum rounding (measure a commuting set), which is how the one-qudit case is
   proved.
4. *Facet reduction plus exact odd cycles (w6-078, 2026-09-18) - partial success.* Restricting the dual
   certificate `Q` to the support of `y_+` reduces (**) to single facet weights on induced subgraphs
   (`hermitian-edge-trace-norm-via-stab-facets`, both directions). Odd holes are solved exactly:
   `min ||C||_1 = 2 cot(pi/(2n)) >= sqrt3 (n+1)/2` on `C_n` (gauge to one flux, shift-average the
   moduli by convexity, concavity of `sum |cos|` between breakpoints). With chord splitting this proves
   (**) for all h-perfect graphs with `omega <= 3`, including all t-perfect graphs
   (`hermitian-edge-trace-norm-k4-free-h-perfect`), and shows that (**) on perfect/h-perfect graphs is
   equivalent to the uniform clique inequality `hermitian-edge-trace-norm-clique-inequality`. The
   remaining holes are that inequality (`K_4` is the first open case; numerical minima `2 + 2 sqrt3`,
   `5 + sqrt5` at `m = 4, 5`) and the non-clique, non-hole facets
   (`hermitian-edge-trace-norm-other-stab-facets`).
5. *Rank-one reduction plus a Yudin-type energy LP (w6-078, 2026-09-18). Large cliques are solved; an
   obstruction is proved at `m = 4, 5`.* Write `C = C_+ - C_-`, and let `d` be the common diagonal.
   Einollahzadeh's modulus lemma, together with the Schur product `conj(C_+) o C_-`, gives unit vectors
   with Gram matrix `G` such that `d_i d_j |1 - G_ij|^2 >= 1`. Averaging over the edges of `K_m` gives
   `||C||_1 >= 2E(G)/(m-1)`, with `E(G) = sum 1/|1-G_ij|`. An explicit positive-definite-kernel
   certificate, checked by interval arithmetic, then proves the clique inequality `||C||_1 >= sqrt3 (m-1)`
   for every `m >= 6` (`hermitian-edge-trace-norm-clique-inequality-large-m`). That is, (**) holds on
   `K_m` with unit weights for `m >= 6`.

   The same route dies at `m = 4, 5`, and this is proved, not only observed. The LP value equals the
   true minimum of `E`, which is attained by the 4th and 5th roots of unity. These minima are
   `2 + 4 sqrt2 = 7.657 < 7.794` and `13.764 < 13.856`, the needed values `(sqrt3/2)(m-1)^2`. So no argument that goes through uniform averaging can
   close them. The loss-free replacement is the fractional-matching statement `(M_m)`:
   `2 nu_f(1/|1-G_ij|) >= (sqrt3/2)(m-1)`. Its numerical minima are `1 + sqrt3` and `(5 + sqrt5)/2`,
   exactly half the minima of `||C||_1`. The open core of the clique case is now `(M_4)` and `(M_5)`, a
   statement about the best perfect matching of 4 (or 5) unit vectors. By the facet reduction, weighted cliques are
   open only through `m = 4, 5`. The non-clique, non-hole facets are also still open.
6. *Flux-torus branch-and-bound with exact SDP-dual certificates (w6-078, 2026-09-18). `K_4` is
   solved.* Gauge the star at one vertex to be real. For fixed phases, `min_{t >= 1} ||C||_1` is an SDP,
   and a dual `Z` with `||Z||_op <= 1` gives the edge-separable bound `sum t_ij 2Re(Z_ji e^{i theta_ij})`.
   Its exact minimum over a phase box and over `t in [1, T]` closes the box. Moduli above `T` are handled
   by `2 x 2` compression. For `m = 4`, 584 boxes with rational, exactly checked `Z` cover the flux torus
   `T^3` (`hermitian-edge-trace-norm-clique-inequality-k4`). The clique inequality is therefore open only
   at `m = 5`. The same script on `T^6` handles it: one sixteenth of the symmetry-reduced domain closes
   with about 41,000 SDP solves, and the full run is in progress. If `m = 5` closes, Theorem C gives
   (**) for every h-perfect graph, including every perfect graph. The non-clique, non-hole facets would
   then be all that remains.
