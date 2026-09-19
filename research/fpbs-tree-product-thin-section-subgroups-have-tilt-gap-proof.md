---
rg: 2
id: fpbs-tree-product-thin-section-subgroups-have-tilt-gap-proof
kind: route
title: Radial symmetry of the two-point function in the tree coordinate, the sphere sum of the half tilt, and coset-by-coset domination of the subgroup susceptibility
target: fpbs-tree-product-thin-section-subgroups-have-tilt-gap
requires:
  - fpbs-hutchcroft-nonunimodular-pc-below-pt
  - fpbs-relative-gap-along-any-subgroup-separates
artifacts:
  - experiments/fpbs-tilt-sections-2026-09-17/check_tilt_sections.py
  - experiments/fpbs-tilt-sections-2026-09-17/output.txt
---

Complete written proof. Notation is as in the target. `tau_p(x,y)` is the
two-point function of Bernoulli(`p`) bond percolation on `G`. `|y|` is the
word length of `y in Lambda`, which is the tree distance from `1` to `y`.
Every sum below has nonnegative terms, so sums may be reordered freely.

## Step 0. The group `Gamma_xi` and its modular function

This step repeats Step 0 of
`fpbs-tree-product-fibre-operator-half-tilt-proof` so that the route is
self-contained.

**Parents and heights.** For `u in T`, the **parent** of `u` is its neighbour
on the ray from `u` to `xi`. Its other `q` neighbours are its **children**.
For `u, v in T`, let `h(u,v)` be the number of parent steps minus the number
of child steps along the geodesic from `u` to `v`.

**The group acts transitively.** `Aut_xi(T) x H_grp` acts coordinatewise, with
`H_grp` acting on `H` by left multiplication. It preserves the edges of the
Cartesian product, so it lies in `Aut(G)`. It is transitive, because
`Aut_xi(T)` is transitive on `T`. The stabiliser of `(x_T,x_H)` is
`Stab_xi(x_T) x {1}`.

**The modular function.** With the import's definition
`Delta(x,y) = |Stab_y x| / |Stab_x y|`, we get
`Delta((x_T,x_H),(y_T,y_H)) = Delta_T(x_T,y_T)`. Let `c` be a child of `u`.

- `Stab_xi(u)` permutes the children of `u` transitively.
- `Stab_xi(c)` fixes the ray from `c` to `xi`, and that ray contains `u`.

So `Delta(c,u) = q`. By the cocycle identity,

```text
Delta(o,(y,h)) = q^(h(1,y)).                                            (0.1)
```

Since `q >= 2`, `Gamma_xi` is nonunimodular. Hence

```text
chi_(p,1/2) = sum_((y,h)) tau_p(o,(y,h)) q^(h(1,y)/2).                  (0.2)
```

## Step 1. Radial symmetry in the tree coordinate

Let `phi in Aut(T)` fix `1`. Then `phi x id_H` is an automorphism of the
Cartesian product `G` that fixes `o`. Bernoulli percolation is invariant under
it, so

```text
tau_p(o,(y,h)) = tau_p(o,(phi y,h)).
```

The stabiliser of a vertex in the automorphism group of a regular tree is
transitive on each sphere about that vertex. To see this, let `|y| = |y'|`.
Build `phi` level by level from `1`. At each vertex `v`, with image `phi(v)`
already fixed, choose a bijection from the neighbours of `v` farther from `1`
onto those of `phi(v)`. There are `k` of these at `1` and `q` elsewhere.
Choose it to send the next vertex of the geodesic `[1,y]` to the next vertex
of `[1,y']` whenever `v` lies on `[1,y]`. So `tau_p(o,(y,h))` depends only on
`|y|` and `h`. Write

```text
tau_p(o,(y,h)) = f_p(|y|,h).                                            (1.1)
```

This uses `Aut(T)`, not `Gamma_xi`. Only `Delta` comes from `Gamma_xi`.

## Step 2. The sphere sum of the half tilt

Let `S(m) = sum_(y in S_m) q^(h(1,y)/2)`. Classify `y in S_m` by the number
`j` of parent steps at the start of the geodesic from `1` to `y`. A parent
step taken right after a child step would return to the previous vertex, so
it would backtrack. Hence the geodesic is `j` parent steps followed by `m-j`
child steps, and `h(1,y) = 2j - m`. The number of such `y` is:

- `q^m` when `j = 0`;
- `(q-1) q^(m-j-1)` when `0 < j < m`, since the first child step must avoid
  the vertex just left;
- `1` when `j = m`.

So, for `m >= 1`,

```text
S(m) = q^m q^(-m/2) + sum_(0<j<m) (q-1) q^(m-j-1) q^(j-m/2) + q^(m/2)
     = q^(m/2) (2 + (m-1)(q-1)/q),
```

and `S(0) = 1`. Moreover

```text
2 + (m-1)(q-1)/q - (m+1)(q-1)/q = 2/q > 0,
```

so for every `m >= 0`

```text
S(m) >= ((q-1)/q) (m+1) q^(m/2).                                        (2.1)
```

The script in `artifacts` checks the formula for `S(m)` exactly on the
Cayley trees of `F_2` (`q = 3`, `m <= 7`) and `F_3` (`q = 5`, `m <= 5`). It
computes `h` from the Busemann function of the end `a^(+infinity)`.

By (0.2), (1.1) and grouping `y` by spheres,

```text
chi_(p,1/2) = sum_(h in H_grp) sum_(m >= 0) f_p(m,h) S(m).              (2.2)
```

**General tilt.** Let `lambda in (0,1)`, `M = max(lambda,1-lambda)`, and
`S_lambda(m) = sum_(y in S_m) q^(lambda h(1,y))`, so that `S_(1/2) = S`.
Write `N_j` for the counts above: `N_0 = q^m`, `N_m = 1`, and
`N_j <= q^(m-j)` for all `j`. Then
`S_lambda(m) = sum_j N_j q^(lambda(2j-m))`.

- *Lower bound.* The `j = 0` term is `q^((1-lambda)m)` and the `j = m` term
  is `q^(lambda m)`.
- *Upper bound.* Each term is at most `q^((1-lambda)m + (2 lambda - 1) j)`.
  The exponent is linear in `j in [0,m]`, so each term is at most `q^(Mm)`.

Hence

```text
q^(Mm) <= S_lambda(m) <= (m+1) q^(Mm),                                  (2.3)
chi_(p,lambda) = sum_(h in H_grp) sum_(m >= 0) f_p(m,h) S_lambda(m).    (2.4)
```

(2.4) follows from `Delta(o,(y,h))^lambda = q^(lambda h(1,y))` and (1.1), in
the same way as (2.2). The script also checks (2.3) numerically for several
`lambda`.

## Step 3. Coset-by-coset domination (Theorem, item 1)

Let `J = J(I)`. For `h in H_grp`, put `I_h = {y in Lambda : (y,h) in I}`.

**Each `I_h` is empty or a left coset of `J`.** If `(y,h), (y',h) in I`, then
`(y,h)^(-1)(y',h) = (y^(-1) y', 1) in I`, so `y^(-1) y' in J`. Conversely,
`(y,h)(j,1) = (yj,h) in I` for every `j in J`. So `I_h = y_h J` for any
`y_h in I_h`.

Let `C' = sup_(h,m) #(I_h ∩ S_m) / ((m+1) q^(m/2))`. Using (1.1), then the
definition of `C'`, then (2.1) and (2.2):

```text
chi^I_p = sum_(h : I_h nonempty) sum_(m >= 0) f_p(m,h) #(I_h ∩ S_m)
       <= C' sum_h sum_m f_p(m,h) (m+1) q^(m/2)
       <= (q/(q-1)) C' sum_h sum_m f_p(m,h) S(m)
        = (q/(q-1)) C' chi_(p,1/2).
```

This holds for every `p in [0,1]`, with both sides possibly infinite. The
same computation with `C = sup_(h,m) #(I_h ∩ S_m) q^(-Mm)`, using the lower
bound in (2.3) and then (2.4), gives

```text
chi^I_p <= C sum_h sum_m f_p(m,h) q^(Mm) <= C chi_(p,lambda).            (3.1)
```

This proves item 1.

## Step 4. The gap (Theorem, item 2)

Let `I` be infinite, `beta(I) < q`, and `lambda in (0,1)` with
`q^M > beta(I)`, where `M = max(lambda,1-lambda)`.

**The constant `C` is finite.** Pick `b` with `beta(I) < b < q^M`. By the
definition of `beta` as a limsup, there is `m_0` such that
`sup_h #(I_h ∩ S_m) <= b^m <= q^(Mm)` for `m >= m_0`. For `m < m_0`,
`#(I_h ∩ S_m) <= |S_m|`. So `C < infinity`, and (3.1) holds.

**Finiteness below the tilted threshold.** By the import (verbatim, line
502), `p_c(G,Gamma_xi,lambda) = sup{p : chi_(p,lambda) < infinity}`. The
function `tau_p` is nondecreasing in `p` (standard monotone coupling), so
`chi_(p,lambda)` is too. Hence `chi_(p,lambda) < infinity` for every
`p < p_c(G,Gamma_xi,lambda)`, and by (3.1) so is `chi^I_p`. So
`sup{p : chi^I_p < infinity} >= p_c(G,Gamma_xi,lambda)`.

**The Hutchcroft–Pan form.** Let `p` be a parameter with
`chi^I_p < infinity`.

- For `v in I`, left multiplication by `v` is an automorphism of `G` that
  maps `I` onto `I`. So `E_p|K_v ∩ I| = chi^I_p < infinity`.
- Hence, almost surely, every cluster of a vertex of `I` meets `I` finitely.
- A cluster that meets `I` is the cluster of one of its vertices in `I`, and
  `I` is countable. So almost surely no cluster meets `I` infinitely often.

So Hutchcroft–Pan's threshold is also at least `p_c(G,Gamma_xi,lambda)`.

**Strictness.** The import (thm:pcpt) applies to the transitive
nonunimodular `Gamma_xi` of Step 0 and gives
`p_c(G) < p_c(G,Gamma_xi,lambda) <= p_t`.

Pick `p in (p_c(G), p_c(G,Gamma_xi,lambda))`. Then `chi^I_p < infinity`, and
item 2 of `fpbs-relative-gap-along-any-subgroup-separates` gives
`p_c(G) < p_c(I;G)`, together with `p_c(G) < p_u(G)`. That last conclusion
was already known on `T x H`.

**The bound `p_t`.**

- If `beta(I) < sqrt q`, take `lambda = 1/2`. Then
  `p_c(G,Gamma_xi,1/2) = p_t` (import, line 509).
- If only `C' < infinity`, the half-tilt inequality of Step 3 replaces (3.1),
  and the same argument gives `p_c(I;G) >= p_t`.

## Step 5. Computing section growth (Theorem, item 3)

Throughout, `J = J(I)`, and by Step 3 every nonempty `I_h` is a left coset
`gJ`.

### (a) Finite and virtually cyclic `J`

**(a1) Finite `J`.** `#(gJ ∩ S_m) <= |J|` for all `g` and `m`.

**(a2) Infinite cyclic `J = <c>`.** Write `d` for the tree metric. Vertices of `T`
are elements of `Lambda`, and `Lambda` acts freely on them by left
multiplication. The coset `gJ = {g c^n}` is the orbit of the vertex `g` under
`c' = g c g^(-1)`, which has infinite order, and `n -> c'^n g` is injective.

*`c'` has an axis.*

- Pick a vertex `x_0` minimising `d(x, c'x)`, and put `l = d(x_0, c'x_0)`.
  Freeness gives `l >= 1`.
- Suppose the geodesics `[x_0, c'^(-1) x_0]` and `[x_0, c'x_0]` share their
  first edge `x_0 y`. Then `c'y` is the vertex of `[c'x_0, x_0]` next to
  `c'x_0`.
  - If `l >= 2`, both `y` and `c'y` lie on `[x_0, c'x_0]`, and
    `d(y, c'y) = l - 2 < l`. This contradicts minimality.
  - If `l = 1`, then `y = c'x_0` and `c'y = x_0`. So `c'^2` fixes `x_0`, and
    freeness gives `c'^2 = 1`. This contradicts infinite order.
- So the translates `c'^n [x_0, c'x_0]` join without backtracking. Their union
  is a bi-infinite geodesic `A`, and `c'` translates `A` by `l`.

*Projections.* Let `pi(x)` be the nearest point of `A` to `x`. Put
`s = d(1, A)` and `r = d(g, A)`. Since `c'` preserves `A` and `d`,
`pi(c'^n g) = c'^n pi(g)` and `d(c'^n g, A) = r`. The points `c'^n pi(g)` are
pairwise distinct points of the line `A`. In a tree, if
`pi(x) ≠ pi(1)`, then

```text
d(1,x) = s + d(pi(1), pi(x)) + d(x, A).
```

This holds because the geodesic from `1` to `x` enters `A` at `pi(1)` and
leaves it at `pi(x)`.

*Counting.* Let `m >= 0`.

- At most one `n` has `c'^n pi(g) = pi(1)`.
- Every other `n` with `d(1, c'^n g) = m` has
  `d(pi(1), c'^n pi(g)) = m - s - r`. On a line, at most two distinct points
  lie at a given distance from `pi(1)`.

So `#(gJ ∩ S_m) <= 3` for all `g` and `m`. The script in `artifacts` finds
the maximum to be at most `2` in 25 test cases.

**(a3) Virtually cyclic `J`.** Let `Z <= J` be infinite cyclic of index `r`,
so that `J = j_1 Z ∪ ... ∪ j_r Z`. Then `gJ` is a union of the `r` cosets
`(g j_i) Z`, each of which meets `S_m` in at most `3` points by (a2). So
`#(gJ ∩ S_m) <= 3r`.

**Conclusion of (a).** In all three cases `sup_(h,m) #(I_h ∩ S_m) =: B` is
finite. Hence `beta(I) <= lim B^(1/m) = 1`, and
`C' <= B / inf_m ((m+1) q^(m/2)) = B < infinity`.

### (b) `J` infinite of finite index in `pi_1(I)`

Let `pi_1(I) = {y : (y,h) in I for some h}`, a subgroup of `Lambda`, and
suppose `J` is infinite with `pi_1(I) = g_1 J ∪ ... ∪ g_r J`. Put
`L = max_i |g_i|` and `alpha = alpha(J)`.

- Every nonempty `I_h` is `y_h J` with `y_h in pi_1(I)`, so it is one of the
  cosets `g_i J`.
- If `x = g_i j` then `| |x| - |j| | <= |g_i| <= L` by the triangle
  inequality. The map `j -> g_i j` is injective, so
  `#(g_i J ∩ S_m) <= sum_(|t - m| <= L) #(J ∩ S_t)`.
- `J` is infinite and spheres are finite, so `#(J ∩ S_t) >= 1` for infinitely
  many `t`, and `alpha >= 1`.
- Fix `epsilon > 0`. There is `C_epsilon` with
  `#(J ∩ S_t) <= C_epsilon (alpha + epsilon)^t` for all `t`. Since
  `alpha + epsilon > 1`,

  ```text
  sup_h #(I_h ∩ S_m) <= (2L+1) C_epsilon (alpha + epsilon)^(m+L).
  ```

  Taking `m`-th roots and `limsup`, `beta(I) <= alpha + epsilon`.
- Conversely `I_1 = J`, so `sup_h #(I_h ∩ S_m) >= #(J ∩ S_m)` and
  `beta(I) >= alpha`.

So `beta(I) = alpha(J(I))`. For `I = J x K` one has `pi_1(I) = J = J(I)`, with
`r = 1`.

## Step 6. The instances

- **Diagonal `D = {(g,g)} <= F_d x F_d`**, with `d >= 2` so that `k = 2d >= 4`.
  - `(y,1) in D` forces `y = 1`, so `J(D) = {1}`.
  - `D` is infinite.
  - `D` is not normal: `(a,1)(b,b)(a^(-1),1) = (a b a^(-1), b)`, which is not
    in `D`, since `a b a^(-1) ≠ b` in `F_d`.
  - `D` is not co-amenable. `D(g,h) -> g^(-1) h` is a well-defined bijection
    from right cosets to `F_d`, because
    `(x,x)(g,h) -> g^(-1) x^(-1) x h = g^(-1) h`. Right multiplication by
    `(1,s)` becomes `w -> ws`. So a `Gamma`-invariant mean on the coset space
    would be a right-invariant mean on `F_d`, and `F_d` is nonamenable.
- **Graph of `psi: H_0 -> Lambda`.** `(y,1) = (psi(h),h)` forces `h = 1` and
  `y = 1`. It is infinite when `H_0` is.
- **`J x H_0`.** Its tree section is `J`.
- **Virtually cyclic `I`.** `J(I)` is isomorphic to a subgroup of `I`. Let
  `Z <= I` be infinite cyclic of finite index.
  - If `J(I) ∩ Z` is trivial, then `J(I)` embeds in a finite set of cosets,
    so it is finite.
  - Otherwise `J(I) ∩ Z` is infinite cyclic of finite index in `J(I)`.

  Either way Step 5(a) applies. For a cyclic `I = <(a,b)>` with `b` of
  infinite order, `J(I) = {1}`.
- **`J x K` with `J <= F_d = Lambda` not co-amenable, `K <= H_grp` arbitrary.**
  - If `J` is finite, then `J = {1}` because `F_d` is torsion-free, and Step
    5(a) applies. Assume `J` infinite.
  - By Step 5(b), `beta(J x K) = alpha(J)`.
  - By items 3 and 2 of `fpbs-tree-subgroup-relative-gap-iff-not-co-amenable`,
    `R_J > 1/q`. By Cauchy–Hadamard `alpha(J) = 1/R_J`, so `alpha(J) < q`.
  - Example: `J = <a,b> <= F_3`, `q = 5`, `K = {1}`, in `F_3 x Z`. Here
    `J ∩ S_m` is the set of reduced words of length `m` in `a^(±1), b^(±1)`, so
    `#(J ∩ S_m) = 4 * 3^(m-1)` (checked by the script for `m <= 6`) and
    `alpha(J) = 3`. This is directly below `q = 5`, without the tree node.
    Since `3 > sqrt 5`, `#(J ∩ S_m)/((m+1) 5^(m/2))` is unbounded, so
    `C' = infinity` and the half-tilt hypothesis fails. Any `lambda` with
    `5^(max(lambda,1-lambda)) > 3`, for example `lambda = 0.2`
    (`5^0.8 ≈ 3.62`), satisfies item 2.
  - `<a> x H_grp` is not normal, since `b a b^(-1)` is not in `<a>`.
- **`N_1 x K` with `N_1` normal in `F_d`, `F_d/N_1` nonamenable, `K` normal in
  `H_grp`, and `N_1 x K` infinite.**
  - It is normal, and its quotient `(F_d/N_1) x (H_grp/K)` surjects onto the
    nonamenable `F_d/N_1`, so it is nonamenable.
  - `N_1` is not co-amenable in `F_d`. Right cosets of `N_1` are the elements
    of the group `F_d/N_1`, and right multiplication by `s in F_d` is right
    translation by its image. So an `F_d`-invariant mean on
    `ℓ^∞(N_1 \ F_d)` would be a right-invariant mean on `F_d/N_1`, which is
    not amenable.
  - So the previous instance applies with `J = N_1`.

## Step 7. Calibration on the tree (Theorem, item 4)

Let `H` be trivial, so `G = T`, `Gamma_xi = Aut_xi(T)`, and `h(1,y)` is as in
Step 2. Here `p_c(J;T)` is the susceptibility threshold
`sup{p : chi^J_p < infinity}`.

- On a tree, `o` and `y` are connected iff every edge of the geodesic is open,
  so `tau_p(o,y) = p^|y|`. By (2.4) with `H` trivial,
  `chi_(p,lambda) = sum_m p^m S_lambda(m)`.
- By (2.3), `q^(Mm) <= S_lambda(m) <= (m+1) q^(Mm)`. So the series converges
  for `p < q^(-M)` and has terms at least `1` at `p = q^(-M)`. Hence
  `p_c(T,Aut_xi T,lambda) = q^(-M)`. At `lambda = 1/2` this is
  `p_t = q^(-1/2)`.
- By item 1 of `fpbs-tree-subgroup-relative-gap-iff-not-co-amenable`,
  `chi^J_p = F_J(p) = sum_t #(J ∩ S_t) p^t`, a power series with nonnegative
  coefficients. So `p_c(J;T) = R_J = 1/alpha(J)` by Cauchy–Hadamard.
- Hence `p_c(J;T) >= p_c(T,Aut_xi T,lambda)` iff `1/alpha(J) >= q^(-M)`, that
  is, iff `alpha(J) <= q^M`.
- As `lambda` ranges over `(0,1)`, `M` ranges over `[1/2,1)` and `q^M` over
  `[sqrt q, q)`. So some `lambda` gives the bound iff `alpha(J) < q`. With
  `H` trivial, `beta = alpha(J)` by Step 5(b), so item 2 gives the bound in
  exactly the same cases.
- `alpha(J) < q` iff `R_J > 1/q` iff `rho_J < 1` (item 2 of the tree node), iff
  `p_c(T) < p_c(J;T)`. So the tilt family certifies exactly the subgroups
  with a gap.
- The half tilt gives the bound iff `alpha(J) <= sqrt q`. The example
  `<a,b> <= F_3` of Step 6, with `alpha = 3 > sqrt 5`, has a gap that the half
  tilt misses.

This completes the proof.
