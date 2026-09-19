---
rg: 2
id: thompson-f-32-term-cogrowth-bound-is-the-moment-optimum-proof
kind: route
title: Truncated multiplication operator on polynomials of degree 15 realises both the bound and its ceiling
target: thompson-f-32-term-cogrowth-bound-is-the-moment-optimum
requires: [even-degree-localizing-hankel-attains-truncated-moment-optimum]
artifacts:
  - experiments/thompson-f-cogrowth-2026-09-18/moment_ceiling.py
  - experiments/thompson-f-cogrowth-2026-09-18/moment_ceiling.json
  - experiments/thompson-f-cogrowth-2026-09-18/jacobi_ceiling.py
  - experiments/thompson-f-cogrowth-2026-09-18/jacobi_ceiling.json
  - experiments/thompson-f-cogrowth-2026-09-18/f_elements.py
  - experiments/thompson-f-cogrowth-2026-09-18/f_elements_selftest.json
  - experiments/thompson-f-cogrowth-2026-09-18/ball_eigen.py
  - experiments/thompson-f-cogrowth-2026-09-18/ball_eigen.json
  - experiments/thompson-f-cogrowth-2026-09-18/ball_boundary.py
  - experiments/thompson-f-cogrowth-2026-09-18/isoperimetric.json
  - experiments/thompson-f-cogrowth-2026-09-18/exchange_rate.py
  - experiments/thompson-f-cogrowth-2026-09-18/exchange_rate.json
---

**Audit note (2026-09-18).** Referee lenses 2 and 3 refuted this route as a complete
direct proof of its target; it is kept as the attempt and the target is back to OPEN. All
three referees independently reproduced and confirmed the headline `N = 31` construction
(steps 2-5): `J` symmetric, `J^i e_0 = x^i/sqrt(M_0)` for `i <= 15`,
`<J^k e_0, e_0> = M_k/M_0` for **every** `k <= 31` including the `k = 31` trick, `e_0`
cyclic so all 16 weights positive, `A(theta)` positive definite iff
`lambda_max(J) < theta`, and the exact rational bisection to width `2^-44`. What failed:

- **Step 6 is an unnamed import (lens 2).** Optimality at *even* `N` is cited to "the
  classical even-degree Hausdorff condition" with no author, reference or statement, and
  the hypotheses actually needed are not those of that name (moving interval `[0, theta]`,
  joint positivity with the Hankel matrix, closedness of the truncated moment cone). That
  step is now the open prerequisite
  `even-degree-localizing-hankel-attains-truncated-moment-optimum`. The even rows remain
  valid **lower** bounds; only their optimality is unproved. Item 4's tree calibration is
  affected the same way, being checked only at even `r`.
- **Step 8's artifact carried the inequality backwards (lens 2, decisive).** The docstring
  of `ball_boundary.py` asserted `||P|| >= sqrt(1 - (b(A)/4)^2)` "proved in the route node
  of this experiment", which is the negation of what step 8 proves; with the node's own
  `b = 1.40743` that false formula yields `||P|| >= 0.9361`, exceeding the node's own
  certified value. Corrected in place 2026-09-18 (no stored JSON was affected: the formula
  never reached the code).
- **The Schreier bullet priced its accelerator by inverting an inequality (lens 3).** See
  the target's `## Attempts`; `|Hg cap B_r| <= |H cap B_{2r}|` gives a *lower* bound
  `|Sch_r| >= |B_r|/|H cap B_{2r}|`, so the honest figure from the measured rates is about
  `1.26` per radius, not `1.85`, and `schreier_feasibility.json`'s own pass criterion is
  not met (`coset_growth_last = 3.02 > 2.76`). Corrected in place 2026-09-18.

Steps 1-5 and 7 below are unchanged and were found sound.

Throughout `P = (x_0 + x_0^{-1} + x_1 + x_1^{-1})/4` on `l^2(F)`, `mu_2` is the spectral
measure of `P^2` at `delta_e`, `c_n` counts trivial words of length `2n`, and
`M_n = c_n/16^n = <P^{2n} delta_e, delta_e>`. `mu_2` is a probability measure on
`[0, ||P||^2]`, so `sup supp mu_2 <= ||P||^2`.

1. **Data.** `c_0..c_31` are the terms printed by A. Elvey Price and A. J. Guttmann,
   *Numerical studies of Thompson's group F and related groups*, arXiv:1706.07571, abstract
   l.42: "We have also given an improved algorithm for the coefficients of Thompson's group
   $F,$ giving 32 terms of the cogrowth series", table at `Group-growth23-6.tex` l.296-333.
   `moment_ceiling.py` embeds the list and re-reads it from last wave's independent
   transcription in `experiments/thompson-f-cogrowth-2026-09-17/epg_certify.py`
   (`transcription_matches_2026_09_17_script: true`). Rows `n <= 15` agree with this
   repository's own exact PL computation and rows `16..24` with the Haagerup-Haagerup-
   Ramirez-Solano table, both checked in the 2026-09-17 node.

2. **The truncated multiplication operator.** Let `L` be the linear functional on
   `R[x]_{<=31}` with `L(x^j) = M_j`, and `V = R[x]_{<=15}` with the bilinear form
   `<p, q> = L(pq)` (degrees at most 30, so this is defined). Its Gram matrix in the basis
   `1, x, ..., x^15` is the Hankel matrix `(M_{i+j})_{i,j<=15}`, verified positive definite
   by exact `LDL^T` in `moment_ceiling.py`, so `V` is a 16-dimensional Euclidean space. Let
   `pi` be the orthogonal projection onto `V` and

       J : V -> V,   J q = pi(x q).

   - `J` is symmetric: for `q, q'` in `V`, `<Jq, q'> = <xq, q'> = L(x q q')` (degree at most
     31), which is symmetric in `q, q'`.
   - Put `e_0 = 1/sqrt(M_0)`. For `i <= 15`, `J^i e_0 = x^i/sqrt(M_0)`, by induction: for
     `i < 15` the polynomial `x cdot x^i` has degree at most 15, so `pi` does nothing.
   - Hence `<J^k e_0, e_0> = M_k/M_0` for every `k <= 31`. For `k <= 30` write `k = i + j`
     with `i, j <= 15` and use symmetry: `<J^k e_0, e_0> = <J^i e_0, J^j e_0> = L(x^{i+j})/M_0`.
     For `k = 31`, `<J^{31} e_0, e_0> = <J (J^{15} e_0), J^{15} e_0> = L(x cdot x^{15} cdot x^{15})/M_0`.
   - `J >= 0`: `<Jq, q> = L(x q^2) = int x q(x)^2 dmu_2 >= 0` because `mu_2` lives on `[0, oo)`.

3. **A representing measure with 16 atoms.** By the spectral theorem for the symmetric
   matrix `J`, write `J = sum_k lambda_k Pi_k`. Put

       nu = M_0 sum_k <Pi_k e_0, e_0> delta_{lambda_k}.

   This is a positive measure of total mass `M_0 = 1`, supported on the (at most 16)
   eigenvalues of `J`, all of which are `>= 0` by step 2, and by step 2 again
   `int x^k dnu = M_0 <J^k e_0, e_0> = M_k` for every `k <= 31`. So `nu` has **exactly** the
   32 published moments, and `sup supp nu = lambda_max(J)`.
   `jacobi_ceiling.py` prints the exact rational Jacobi data (`a_k`, `b_k^2`), the 16 nodes
   and weights, and checks that this atomic measure reproduces `M_0..M_31` with relative
   error at most `7.4 x 10^-15` in floating point.

4. **The localizing matrix is exactly the operator test.** For `q` in `V` with coefficient
   vector `v`, `<(theta - J)q, q> = L((theta - x) q^2) = v^T A(theta) v` where
   `A(theta)_{ij} = theta M_{i+j} - M_{i+j+1}`, `0 <= i, j <= 15`. Hence

       A(theta) positive definite  <=>  lambda_max(J) < theta,
       A(theta) not positive semidefinite  =>  lambda_max(J) > theta.

5. **Both sides of the claim.**
   - *(lower)* `moment_ceiling.py` bisects with exact `Fraction` arithmetic and returns
     `theta_lo = 14589790647431/17592186044416` together with an explicit integer vector `v`
     with `v^T A(theta_lo) v < 0`, re-evaluated directly. If `mu_2` were supported in
     `[0, theta_lo]` the integrand `(theta_lo - x) q(x)^2` would be non-negative on the
     support, so `int (theta_lo - x) q^2 dmu_2 = v^T A(theta_lo) v >= 0`, a contradiction.
     Hence `||P||^2 >= sup supp mu_2 > theta_lo`, and since
     `(227669384863/250000000000)^2 <= theta_lo` (asserted exactly),
     `||P|| > 0.910677539452`.
   - *(ceiling)* At `theta_hi = theta_lo + 2^-44` the same exact `LDL^T` shows `A(theta_hi)`
     positive definite, so `lambda_max(J) < theta_hi` and the measure `nu` of step 3 is a
     positive measure with the 32 published moments and `sup supp nu < theta_hi`. Therefore
     `min { sup supp nu' : nu' >= 0 with moments M_0..M_31 } = lambda_max(J)` — the minimum
     is attained by `nu` and no smaller value is possible by the argument of the previous
     bullet applied to `nu'`. Consequently every bound on `||P||` that is deduced only from
     the positivity of a measure with these 32 moments is at most
     `sqrt(theta_hi) = 0.9106775394527`.

6. **The table for `N < 31`.** `moment_ceiling.py` repeats the bisection for every `N`. For
   odd `N = 2d+1` the matrix is `(theta M_{i+j} - M_{i+j+1})_{i,j<=d}` and steps 2-5 apply
   verbatim with `V = R[x]_{<=d}`, so the tabulated `theta*(N)` is the exact optimum. For
   even `N = 2d` the script uses `(theta M_{i+j+1} - M_{i+j+2})_{i,j<=d-1}`, the Hankel
   matrix of `x(theta - x)s`; the witness argument still proves the lower bound
   (`x >= 0` on `supp mu_2`), so every even row is a valid **lower** bound. Optimality at
   even `N` is **not** proved here and is not a step of this route: it is the open
   prerequisite `even-degree-localizing-hankel-attains-truncated-moment-optimum` (the
   earlier text cited "the classical even-degree Hausdorff condition" without author,
   reference or statement, and the hypotheses needed are not those of that name). All rows
   used in the fit of item 3 of the claim (`N = 15, 23, 31`) are odd, as is the headline
   `N = 31`, so neither depends on this.

7. **Window certificates and the exchange rate.** For a finite vertex set `A` of
   `Gamma = Cay(F, {x_0^{+-1}, x_1^{+-1}})` and a real vector `v` supported on `A`,
   `<A_Gamma v, v> <= 4 ||P|| <v, v>`, so any integer vector gives an exactly checkable
   lower bound. `f_elements.py` implements `F` twice, as exact PL maps (copied from
   `experiments/thompson-f/cogrowth_exact.py`) and as reduced tree pairs with a canonical
   integer key, and its self-test checks both relators, the round trip between the two
   representations, agreement of the two products on 20000 random words, and the cogrowth
   terms `4, 28, 232, 2092` by brute force. `ball_eigen.py` builds `B_r` with those keys,
   takes the top Dirichlet eigenvector in floating point, rounds it to integers and reports
   the **exact** integer Rayleigh quotient; `ball_eigen.json` gives
   `0.870273` at `r = 12` (`|B_12| = 676061`).
   On the 4-regular tree the same two routes agree to `10^-13` at `r = 4, 6, 8, 10, 12`
   (`exchange_rate.py`, `free_group_routes_agree: true`): there the induced subgraph `B_r`
   is connected, its Perron vector is unique up to scale and therefore invariant under the
   automorphisms fixing the centre, hence radial; the radial subspace is
   `span{delta_o, A delta_o, ..., A^r delta_o}`, whose Rayleigh maximum is the largest node
   of the moment problem with `c_0..c_r`. *Caveat (2026-09-18):* that last identification
   is proved here only for odd truncation, and all five checked radii are even, so the
   agreement is measured but its stated reason inherits the open prerequisite of step 6.
   The measurement itself is unaffected. In `F` the excess of the window over the moment
   bound at `N = r` is `0.000763, 0.001242, 0.001717, 0.002092` at `r = 6, 8, 10, 12`, i.e.
   `+0.00022` per unit radius, while `|B_r|` multiplies by `2.76`. Extrapolating the moment
   fit plus that excess, a ball window first reaches `0.910678` at `r ~ 27`, about
   `3 x 10^12` vertices.

8. **Isoperimetric certificates (recorded as a dead end).** `ball_boundary.py` minimises
   `b(A) = |dA|/|A| = 4 - 2 e(A)/|A|` over subsets of `B_11` by Charikar's min-degree
   peeling followed by exact local search; every count is integer, and every edge of `Gamma`
   inside a subset of `B_{R-1}` is present in the induced subgraph of `B_R`, so the counts
   are the true ones in the infinite graph. Best found: `|A| = 41136`, `e(A) = 53324`,
   `b = 1.40743`. The Kesten-Dodziuk inequality `h <= 4 sqrt(1 - ||P||^2)` turns a *lower*
   bound on `h` into an upper bound on `||P||`; from an upper bound on `h` only the
   elementary side `||P|| >= 1 - b/4 = 0.6481` survives, which is the Rayleigh quotient of
   the indicator vector and is dominated by step 7. This is where the whole isoperimetric
   class dies.
