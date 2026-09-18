---
rg: 2
id: fpbs-boundary-tilted-susceptibility-kernel-proof
kind: route
title: Proof that boundary Radon-Nikodym cocycles carry a tilted mass transport with lambda to 1-lambda duality, that the half tilt forces the worst-pair rate, that trees reach p_2 and that amenable BS(1,2) x Z pins the threshold at p_c
target: fpbs-boundary-tilted-susceptibility-kernel
requires:
  - fpbs-worst-pair-connectivity-rate-kernel
  - fpbs-worst-pair-collapse-realized-on-amenable-growth
  - fpbs-hyperbolic-nonunimodular-critical-l2-gap
  - fpbs-acylindrically-hyperbolic-critical-l2-gap
  - fpbs-lq-two-point-infinite-cluster-reduction
artifacts:
  - experiments/boundary-tilt-2026-09-17/check_boundary_tilt.py
  - experiments/boundary-tilt-2026-09-17/check_boundary_tilt.out
---

Notation is that of the target claim. `Gamma` is countable, so every identity
below that holds `nu`-a.e. for each fixed tuple of group elements holds
simultaneously for all tuples on one conull `Gamma`-invariant set. We fix Borel
versions of the Radon–Nikodym derivatives and work on that set.

Throughout, `p_c` is the threshold where `chi_p` becomes infinite. On a
transitive graph it equals the threshold for an infinite cluster (sharpness,
as used in `fpbs-worst-pair-connectivity-rate-kernel`). By quasi-invariance,
`Delta_zeta(x,y) in (0,infinity)` a.e.

## Item 1: cocycle, invariance and the tilted mass transport

**Cocycle.** `nu_x`, `nu_y` and `nu_w` are mutually absolutely continuous. The
chain rule gives `d nu_w/d nu_x = (d nu_y/d nu_x)(d nu_w/d nu_y)` a.e. Taking
`w = x` gives `Delta_zeta(y,x) = Delta_zeta(x,y)^(-1)` and `Delta_zeta(x,x) = 1`.

**Diagonal invariance.** `nu_(gy) = g_* nu_y` and `nu_(gx) = g_* nu_x`. For a
Borel set `A`,

```text
nu_(gy)(A) = nu_y(g^(-1) A) = int_(g^(-1) A) Delta_eta(x,y) d nu_x(eta)
           = int_A Delta_(g^(-1) zeta)(x,y) d nu_(gx)(zeta),
```

so `Delta_zeta(gx,gy) = Delta_(g^(-1) zeta)(x,y)`. Replacing `zeta` by
`g zeta` gives `Delta_(g zeta)(gx,gy) = Delta_zeta(x,y)`.

**Normalisation.** `int Delta_zeta(o,y) d nu = nu_y(Z) = 1`, because `nu = nu_o`.

**Tilted mass transport.** Let `F >= 0` be measurable and diagonally invariant.
Fix `y`. Invariance with `g = y^(-1)` gives
`F(o,y,zeta) = F(y^(-1),o,y^(-1) zeta)`. Substitute `eta = y^(-1) zeta`; its
law under `nu` is `(y^(-1))_* nu = nu_(y^(-1))`. Then

```text
int F(o,y,zeta) d nu(zeta) = int F(y^(-1),o,eta) d nu_(y^(-1))(eta)
                           = int F(y^(-1),o,eta) Delta_eta(o,y^(-1)) d nu(eta).
```

Summing over `y` and reindexing `y -> y^(-1)` gives the claimed identity. All
terms are nonnegative, so Tonelli allows the exchange and both sides may be
`+infinity`.

The identity uses only that `Gamma` is countable and acts on itself simply
transitively. Unimodularity of `Gamma` plays no role, because the tilt comes
from `nu`, not from a modular function.

## Item 2: duality and convexity

`tau_p(gx,gy) = tau_p(x,y)` because left multiplication is a graph
automorphism. Put `F(x,y,zeta) = tau_p(x,y) Delta_zeta(x,y)^lambda`; it is
nonnegative and diagonally invariant by item 1.

- The left side of the mass transport is `sum_y tau_p(o,y) phi_lambda(y) = chi^nu_lambda(p)`.
- By symmetry of `tau` and `Delta_zeta(y,o) = Delta_zeta(o,y)^(-1)`, the right
  side is

  ```text
  sum_y tau_p(o,y) int Delta_zeta(o,y)^(-lambda) Delta_zeta(o,y) d nu
      = chi^nu_(1-lambda)(p).
  ```

`phi_0 = 1` because `Delta > 0` a.e., and `phi_1 = 1` by normalisation. So
`chi^nu_0 = chi^nu_1 = chi_p`.

**Log-convexity.** Let `mu` be the measure `tau_p(o,y) (counting) x nu` on
`Gamma x Z`. Then `chi^nu_lambda = int Delta^lambda d mu`. For
`lambda = s l_1 + (1-s) l_2` with `s in (0,1)`, Hölder with exponents `1/s` and
`1/(1-s)` gives `chi_lambda <= chi_(l_1)^s chi_(l_2)^(1-s)` in `[0,infinity]`.

**Consequences.**

- With `l_1 = lambda`, `l_2 = 1-lambda` and `s = 1/2`, duality gives
  `chi_(1/2) <= chi_lambda`.
- With `l_1 = 0` and `l_2 = 1`, it gives `chi_lambda <= chi_p` for
  `lambda in [0,1]`.

`tau_p` is nondecreasing in `p`, so each `chi^nu_lambda(p)` is nondecreasing in
`p` and `p^nu_c(lambda)` is a threshold. The two inequalities give
`p_c <= p^nu_c(lambda) <= p^nu_t`. Duality gives
`p^nu_c(lambda) = p^nu_c(1-lambda)`.

## Item 3: the half tilt forces the worst-pair rate

Let `chi^nu_(1/2)(p) < infinity`. By Tonelli,
`int S(zeta) d nu < infinity`, where
`S(zeta) = sum_y tau_p(o,y) Delta_zeta(o,y)^(1/2)`. So `S < infinity` a.e.

Choose `zeta` with `h_nu(zeta) >= h` and `S(zeta) < infinity`. This is possible
because the first set has positive measure. Fix `epsilon in (0,h)`. There are
infinitely many `n` with some `y_n in B_n` satisfying
`Delta_zeta(o,y_n) >= e^((h-epsilon) n)`. For each such `n`,

```text
kappa_p(n) <= tau_p(o,y_n) <= S(zeta) Delta_zeta(o,y_n)^(-1/2) <= S(zeta) e^(-(h-epsilon) n / 2).
```

Hence `limsup_n -(1/n) log kappa_p(n) >= (h-epsilon)/2` for every `epsilon`.

On a nonamenable `G`, item 1 of `fpbs-worst-pair-connectivity-rate-kernel`
says `gamma(p)` is a limit. So `gamma(p) >= h/2`.

**Consequences.**

- For every `p in (p_c,p^nu_t)`, monotonicity gives `chi^nu_(1/2)(p) < infinity`.
  So `gamma(p) >= h/2 > 0`, which is (K), and item 4 of the kernel claim gives
  `p_c < p_u`.
- If `p > p_u`, the infinite cluster is unique and `theta(p) > 0`. Harris–FKG
  then gives `tau_p(o,y) >= theta(p)^2` for all `y`, so `kappa_p(n)` does not
  decay. The display above then forces `chi^nu_(1/2)(p) = infinity`. So
  `p^nu_t <= p_u`.

## Item 4: comparison with the l2 threshold

`pi_nu` is unitary on `L^2(nu)` (the standard Koopman representation), and

```text
<pi_nu(y) 1, 1> = int (d nu_y / d nu)^(1/2) d nu = phi_(1/2)(y) >= 0.
```

Suppose `pi_nu ≺ lambda_Gamma`, meaning weak containment in the left regular
representation. Then `||pi_nu(f)|| <= ||lambda_Gamma(f)||` for every finitely
supported `f`. This is the norm characterisation of weak containment (Dixmier,
C*-algebras, 18.1.4; Bekka–de la Harpe–Valette, Appendix F).

Let `a_R = tau_p(o,.) 1_(B_R) >= 0`. Then

```text
sum_(y in B_R) tau_p(o,y) phi_(1/2)(y) = <pi_nu(a_R) 1, 1> <= ||lambda(a_R)|| <= ||lambda(a)||.
```

The last step holds because `a_R <= a` entrywise and both are nonnegative
kernels: `|<lambda(a_R) f, g>| <= <lambda(a)|f|,|g|>`.

The kernel of `lambda(a)` is `(x,w) -> a(x w^(-1))`. Conjugating by
`J f(x) = f(x^(-1))` turns it into `(x,w) -> a(x^(-1) w) = tau_p(x,w)`, which
is `T_p`. So `||lambda(a)|| = ||T_p||_(2->2)`. Letting `R -> infinity` gives
`chi^nu_(1/2)(p) <= ||T_p||_(2->2)`. In particular, every `p < p_(2->2)` has
`chi^nu_(1/2)(p) < infinity`, so `p_(2->2) <= p^nu_t`.

## Item 5: trees

`G = Cay((Z/2)^(*d), {s_1,...,s_d}) = T_d`, and `Z` is the set of infinite
reduced words. The visual measure from a vertex `x` gives the set of ends
through a vertex `z` at distance `r >= 1` from `x` (away from `x`) mass
`1/(d (d-1)^(r-1))`. Left multiplication is an isometry, so `x_* nu_o` is the
visual measure from `x`.

**RN derivative.** Let `z` lie on the ray to `zeta` beyond the confluence of `o`
and `x`. Then the cylinder at `z` is a shadow from both `o` and `x`, and

```text
nu_x(C_z)/nu_o(C_z) = (d-1)^(-(d(x,z) - d(o,z))) = (d-1)^(-b_zeta(x)).
```

These cylinders generate, so `Delta_zeta(o,x) = (d-1)^(-b_zeta(x))`. Part 1(a)
of the artifact checks this exactly on depth-8 cylinders.

**RN growth.** `min_(y in B_n) b_zeta(y) = -n`, attained at the point at
distance `n` along `zeta`. So `h_nu(zeta) = log(d-1)` for every `zeta`.

**Spherical function.** Let `|y| = n >= 1` and let `k` be the length of the
common prefix of `y` and `zeta`. Then `b_zeta(y) = n - 2k`, and

```text
nu(k = 0) = (d-1)/d,
nu(k = j) = (d-2)/(d (d-1)^j)   for 1 <= j <= n-1,
nu(k = n) = 1/(d (d-1)^(n-1)).
```

So

```text
phi_lambda(y) = (d-1)^(-lambda n) [ (d-1)/d + ((d-2)/d) sum_(j=1)^(n-1) (d-1)^((2 lambda - 1) j) + (d-1)^(2 lambda n - n + 1)/d ].
```

At `lambda = 1/2` the bracket is `(2(d-1) + (n-1)(d-2))/d = (d + n(d-2))/d`,
the Harish-Chandra function. Part 1(b) checks this exactly for `n <= 5`, together
with radiality and the `0.3 <-> 0.7` symmetry.

**Thresholds.** Put `m = min(lambda,1-lambda)` for `lambda in [0,1]`. The bracket
shows `c_d (d-1)^(-m n) <= phi_lambda(n) <= C_d (n+1) (d-1)^(-m n)`.

- The lower bound comes from the `j = 0` term if `lambda <= 1/2`, and from the
  `j = n` term otherwise.
- The upper bound is a geometric-sum estimate.

On a tree `tau_p(o,y) = p^(|y|)`, and `|S_n| = d(d-1)^(n-1)`. So

```text
chi^nu_lambda(p) = 1 + sum_n d (d-1)^(n-1) p^n phi_lambda(n)
```

converges when `p (d-1)^(1-m) < 1`. It diverges when `p (d-1)^(1-m) >= 1`,
because the terms are then bounded below by a positive constant. So
`p^nu_c(lambda) = (d-1)^(-(1-m))`. This is `1/(d-1) = p_c` at `m = 0` and
`(d-1)^(-1/2)` at `m = 1/2`. Part 1(c) prints the sphere terms on both sides of
`p^nu_t`.

Finally `kappa_p(n) = p^n` exactly, so `gamma(p) = -log p`. At
`p = (d-1)^(-1/2)` this equals `(1/2) log(d-1) = h/2`.

## Item 6: BS(1,2) x Z

**(i) Group facts.**

- The relation holds: `t a t^(-1)(x) = 2(x/2 + 1) = x + 2 = a^2(x)`.
- `BS(1,2) = Z[1/2] ⋊ Z` is metabelian, so `H` is amenable.
- *Growth.* Compose maps from left to right as written. For `b_i in {0,1}`, the
  word `a^(b_0) t a^(b_1) t ... a^(b_(n-1)) t` has length at most `2n` and acts
  as `x -> 2^n x + sum_i b_i 2^i`. These `2^n` affine maps are distinct, so the
  elements are distinct and `|B_(2n)| >= 2^n`. Hence
  `gr(H) >= 2^(1/2) >= 2^(1/4)`.
- *Grid.* `<t,z> = Z^2` because `z` is central of infinite order and
  `<t> ∩ <z> = 1`. Its Cayley graph on `{t,z}` is a subgraph of `H`, so
  `p_c(H) <= p_c(Z^2) = 1/2`.

**(ii) The boundary.**

- The Cauchy density `f(x) = 1/(pi(1+x^2))` is positive and smooth, and the
  action is by affine bijections, so `nu` is quasi-invariant. Items 1–2 then
  apply verbatim.
- For `y = g^(-1)`, `Delta_zeta(o,y) = f(g zeta) g'(zeta)/f(zeta)`.
- Given `zeta` and `n >= 1`, put `m = floor(2^n zeta)` and
  `g_n = a^(-m) t^n : x -> 2^n x - m`. Then `g_n zeta in [0,1)`, so

  ```text
  Delta_zeta(o, g_n^(-1)) = 2^n (1 + zeta^2)/(1 + (g_n zeta)^2) >= 2^n (1 + zeta^2)/2.
  ```

- *Length.* Let `B` be the number of binary digits of `|m|`. The Horner word
  `a^(±b_0) t a^(±b_1) t ... a^(±b_(B-1)) t^(-(B-1))` represents `a^(-m)` and has
  length at most `3B - 2 <= 3 log2|m| + 1`. Since `|m| <= 2^n(|zeta| + 1)`,

  ```text
  |g_n^(-1)| = |g_n| <= 4n + 3 log2(|zeta| + 2) + 3 = 4n + C_zeta .
  ```

- *Growth rate.* With `N = 4n + C_zeta`,
  `max_(y in B_N) log Delta_zeta(o,y) >= n log 2 - log 2`. So
  `h_nu(zeta) >= (log 2)/4` for every `zeta`.
- Part 2 of the artifact builds `g_n` letter by letter over the rationals for
  `zeta in {0, 0.37, -2.5, 11.125, pi}` and `n <= 40`, and checks both
  inequalities.

**(iii) The threshold.** Let `p > p_c(H)`. Item 1 of
`fpbs-worst-pair-collapse-realized-on-amenable-growth` gives
`tau_p(o,y) >= theta(p)^2 > 0` for all `y`, so `kappa_p(n) >= theta(p)^2`.
Suppose `chi^nu_(1/2)(p) < infinity`. The display in item 3, which uses no
nonamenability, would then give `kappa_p(n) <= S e^(-(h-epsilon)n/2)` for
infinitely many `n`, with `h = (log 2)/4`. That is a contradiction. So
`chi^nu_(1/2)(p) = infinity`, and together with item 2, `p^nu_t(H) = p_c(H)`.

**General amenable statement.** The argument uses only three facts:

- uniqueness with `tau >= theta^2` above `p_c`, which is item 1 of the
  collapse claim on every amenable Cayley graph with `gr > 1` and `p_c < 1`;
- the display of item 3;
- `nu(h_nu >= h) > 0` for some `h > 0`, which follows from `nu(h_nu > 0) > 0`
  by countable additivity.

## The class kill and the failing step

**Kill.** Let an argument derive `chi^nu_(1/2)(p) < infinity` at some
`p > p_c(G)` using only inputs (a) and (b) of the target claim. Run on
`(H, R, Cauchy)`, all of its inputs hold:

- (a) by item 6 of the collapse claim, since `gr(H) > 1` and `p_c(H) < 1`;
- (b) by items 1, 2 and 6(ii), together with Hulanicki's theorem (every unitary
  representation of an amenable group is weakly contained in the regular one)
  and Zimmer-amenability of every action of an amenable group.

Its conclusion, however, contradicts 6(iii). So the argument is invalid.

**Hutchcroft's route.** Hutchcroft's route gives `p_c < p_c(lambda)` for
`lambda in (0,1)`. Suppose it transferred to boundary cocycles using only (a)
and (b). On `H` it would give
`p_c(H) < p^nu_c(1/3) <= p^nu_t(H) = p_c(H)`. So at least one of its two
components (the tilted Aizenman–Barsky bound or the bootstrap) does not
transfer.

**Rigidity remark.** Suppose `Delta_zeta(o,y) = c(y)` a.e., independent of
`zeta`. By the cocycle identity and diagonal invariance,

```text
c(xy) = Delta_zeta(o,x) Delta_zeta(x,xy) = c(x) Delta_(x^(-1) zeta)(o,y) = c(x) c(y).
```

So `c` is a homomorphism to `(R_(>0), x)`. By normalisation, `c(y) = 1`.

A nontrivial boundary tilt on a Cayley graph with the Cayley group acting is
therefore root-dependent, and translating a layer
`{x : log Delta_zeta(o,x) in [n,n+1)}` by `x^(-1)` moves the root `zeta`.

**Where the transfer breaks (diagnostic, not load-bearing).** Hutchcroft's
supermultiplicativity steps (Section 5.2 of arXiv:1711.02590v3) concatenate
layers. Along a boundary cocycle they need bounds uniform over the orbit of
`zeta`, while items 1–2 control only `nu`-averages. In the nonunimodular setting
`Delta` is a function on `V x V`, so these coincide.

## Remark: the known classes for (K)

Let `G` be a Cayley graph in either of these classes:

- `G` is hyperbolic and nonamenable, or `Aut(G)` has a quasi-transitive
  nonunimodular subgroup, which forces nonamenability;
- the group is acylindrically hyperbolic, which is nonamenable.

In both cases `p_c < p_(2->2)`, by `fpbs-hyperbolic-nonunimodular-critical-l2-gap`
and `fpbs-acylindrically-hyperbolic-critical-l2-gap`. For `p` in
`(p_c, p_(2->2))`,

```text
Z_2(p) = sum_x tau_p(o,x)^2 = ||T_p delta_o||^2 <= ||T_p||^2_(2->2) < infinity.
```

So item (C) of `fpbs-lq-two-point-infinite-cluster-reduction` gives
`gamma(p) >= (log gr)/2`, which is (K). This remark is recorded for calibration.
Items 1–6 do not use it.
