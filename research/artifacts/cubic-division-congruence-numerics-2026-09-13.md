# Numerics: congruence Schreier spectra of a thin free subgroup of a cubic division lattice

Lane `ex-cubic-division-strong-convergence`, 2026-09-13.  This is evidence, not
proof.  It tests the necessary condition in
`cubic-division-congruence-sc-descends-to-thin-subgroups` on explicit sectors
of `l^2_0(SL_3(F_p))`, for an explicit certified free subgroup.

## Setup

**Algebra.**  `K = Q(theta)`, `theta = 2cos(2 pi/7)`, minimal polynomial
`x^3 + x^2 - 2x - 1`, and `sigma(theta) = theta^2 - 2` generating `Gal(K/Q)`.
`D = (K/Q, sigma, 2)`: `D = K + Kx + Kx^2`, `x^3 = 2`, `x alpha = sigma(alpha) x`.
The prime 2 is inert in `K` (2 has order 3 mod 7), so the local invariant at
2 is `v_2(2)/3 = 1/3`.  It has order 3, so `D` has period and index 3 and is a
division algebra.

**Lattice.**  `Lambda = O_K + O_K x + O_K x^2` is an order (`O_K = Z[theta]`).
`Gamma = SL_1(Lambda)` is commensurable with `SL_1(O_D)`: a cocompact Kazhdan
lattice in `SL_3(R)`.  It is torsion-free.  A torsion element `zeta` would
generate a cyclotomic subfield `Q(zeta) <= D` of degree at most 3 containing
no quadratic subfield, which forces `zeta = +-1`, and `Nrd(-1) = -1`.

**Matrix model.**  Left multiplication on the right `K`-space `D` with basis
`1, x, x^2`.  For `u = a0 + a1 x + a2 x^2`:
`L_u = [[a0, 2a2, 2a1], [a1', a0', 2a2'], [a2'', a1'', a0'']]`, where
`' = sigma^-1` and `'' = sigma^-2`, and `Nrd(u) = det L_u`.  The relation
`L_x L_alpha = L_sigma(alpha) L_x` was checked by hand.  The real embedding
uses `theta, sigma^-1 theta, sigma^-2 theta = 2cos(2pi/7), 2cos(6pi/7), 2cos(4pi/7)`.
At a prime `p == +-1 mod 7`, `p` splits in `K`.  Choose a root `r` of the
minimal polynomial mod `p`; the conjugates are `r'' = r^2 - 2` and
`r' = (r'')^2 - 2`.  This gives `Lambda -> M_3(F_p)`, and `det = 1` is checked
in every run.

**Elements.**  `a = L_theta` is a unit of norm one on the split torus
`K^1`.  An exhaustive search over coefficients in `[-1,1]` found 884 norm-one
elements outside `K`.  The code uses the third of them:
`u = (theta - theta^2) + (-theta - theta^2) x + (-1 - theta - theta^2) x^2`.
Put `b = u a u^-1`, `A = a^19` and `B = b^19`.

**Freeness certificate.**  The code runs ping-pong on `P^2(R)` with the
attracting points and repelling planes of `A^(+-1)` and `B^(+-1)`.  Caps of
angle `eps = 0.001476` are pairwise disjoint and mapped into each other; the
contraction ratios are `9.2e-4` for `a^19` and `3.2e-9` for `a^-19`.  So
`<A, B>` is free of rank 2.  It is thin, since it has infinite index in a
Kazhdan group.  This is a floating-point check with explicit perturbation
margins, not interval arithmetic.  The runs also use the uncertified pair
`m = 1` (`A = a`, `B = b`).

**Regular norms.**  For free `A, B` and `z = c1(A + A^-1) + c2(B + B^-1)`,
Lehner's formula gives `||lambda(z)|| = min_t [-t + sqrt(t^2+4c1^2) + sqrt(t^2+4c2^2)]`.
It returns `2 sqrt 3 = 3.464102` for `(1,1)` (Kesten; checked at `k = 1, 2, 3`
against 2, `2 sqrt 3`, `2 sqrt 5`), `5.269364` for `(1,2)`, and the analogous value for
`(1,3)`.  The printed `excess` is the computed norm minus this value.

## Sectors

| space | representation of `SL_3(F_p)` | dimension |
|---|---|---|
| `P^2(F_p)`, mean zero | unipotent `(p^2+p)`-dimensional (degenerate principal series) | `p^2+p` |
| Legendre-twisted sections over `P^2(F_p)` | `Ind_P^G(chi o det)`, `chi` quadratic (odd degenerate series) | `p^2+p+1` |
| flags `G/B`, mean zero | `2 (p^2+p)` plus Steinberg | `(p^2+p+1)(p+1) - 1` |

Cuspidal and other generic series appear only in permutation spaces of size
about `p^5`.  One such space was computed at `p = 29`: nondegenerate conics,
restricted to one `SL_3`-orbit.  See the section on the conic space below.

## Method

Lanczos without reorthogonalization: `k = 600` steps, random start, constants
projected out at each step for untwisted spaces.  The extreme eigenvalues of
the tridiagonal matrix are found by Sturm bisection.  Ritz values never exceed
the true extreme eigenvalues (up to rounding), so a positive `excess` is a real
outlier.  A negative `excess` of about `1e-4` is Lanczos shortfall at `N ~ 1e6`.
The code checks that each permutation and its inverse are mutually inverse.

Two controls: ctl 1 replaces `B` by a random `SL_3(F_p)`-conjugate of `A`
(same element orders), and ctl 2 takes `A, B` Haar-random in `SL_3(F_p)`.
The primes are all `p == +-1 mod 7` with `29 <= p <= 967` (55 primes) for
`P^2`, and `29 <= p <= 139` for flags (`N` up to `2.7e6`).

## Results (excess over the regular norm)

Group summaries.  For `P^2` the statistics are over `p >= 300` (36 primes);
for flags over `p >= 97` (4 primes).

| sector | pair | mean | max (prime) |
|---|---|---|---|
| `P^2` untwisted | arithmetic `m=19` | -0.00004 | +0.00256 (419) |
| `P^2` untwisted | arithmetic `m=1` | -0.00013 | +0.00024 (617) |
| `P^2` untwisted | conjugate control | -0.00002 | +0.00348 (419) |
| `P^2` untwisted | random | -0.00007 | +0.00027 (503) |
| `P^2` Legendre | arithmetic `m=19` | -0.00002 | +0.00300 (419) |
| `P^2` Legendre | arithmetic `m=1` | -0.00009 | +0.00058 (307) |
| `P^2` Legendre | conjugate control | +0.00001 | +0.00394 (419) |
| `P^2` Legendre | random | -0.00013 | +0.00042 (631) |
| `P^2`, `c = (1,2)` | arithmetic `m=19` | -0.00004 | +0.00408 (419) |
| `P^2`, `c = (1,2)` | random | -0.00001 | +0.00112 (449) |
| `P^2`, `c = (1,3)` | arithmetic `m=19` | +0.00003 | +0.00595 (419) |
| `P^2`, `c = (1,3)` | random | -0.00001 | +0.00166 (307) |
| flags | arithmetic `m=19` | -0.00005 | +0.00005 (113) |
| flags | conjugate control | +0.00031 | +0.00097 (127) |
| flags | random | -0.00003 | +0.00013 (139) |

Selected primes, `P^2` untwisted (arithmetic `m=19`, arithmetic `m=1`, conjugate, random):

| p | N | excesses |
|---|---|---|
| 97 | 9507 | -0.00112, -0.00272, -0.00412, -0.00108 |
| 421 | 177663 | -0.00061, -0.00030, -0.00057, -0.00031 |
| 701 | 492103 | +0.00025, -0.00025, -0.00004, +0.00003 |
| 967 | 936057 | +0.00007, -0.00007, -0.00012, -0.00000 |

At `p <= 43` (`N <= 2000`) every column fluctuates by up to `+-0.02`, the
random controls included.  That is finite size.  The flag run at `p = 13`
gave `+0.077`.

## The `p = 419` transient

`p - 1 = 418 = 2 * 11 * 19`.  The conjugates of `theta` mod 419 have orders
209, 418 and 418, and their 19th powers have orders 11, 22 and 22.  So `A = a^19`
has order 22 mod 419, and the reduced pair is a quotient of `Z/22 * Z/22`.
That is a proper quotient of `F_2` with nonamenable kernel, so its regular norm
is strictly larger than `2 sqrt 3` (Kesten).  Three checks agree:
- the conjugate control, which shares `A`, shows the same excess;
- the `m = 1` pair at 419, where `A` has order 418, shows `+0.00012`;
- the random pairs show nothing.

Along primes, every nontrivial element has order tending to infinity.  If
`theta^n == 1` mod a prime above `p`, then `p <= |N(theta^n - 1)| <= (1 + 1.802^n)^3`,
so `n >= log p / (3 log 1.802) - O(1)`, and `a^m` has order at least
`ord(theta)/m`.  The transient is therefore consistent with strong
convergence.  What it records is that convergence is slow along primes where
a fixed high power has small order.

## The conic space at `p = 29` (a sector that should contain cuspidals)

**Space.**  `SL_3(F_p)` acts on nondegenerate conics, i.e. symmetric `3 x 3`
matrices up to scalars with `S -> g S g^T`.  The invariant `det S` modulo
cubes separates orbits.  At `p == 1 mod 3` there are three orbits, and the
first run at `p = 13` showed the extra invariant vectors as the eigenvalue
`4.000000`.  The code keeps the orbit with `det S` a cube.  At `p = 29`
(`29 == 2 mod 3`) that is all nondegenerate conics, `N = 20510308`.

**Does it contain cuspidals?**  The permutation module of `GL_3(F_q)` on all
nondegenerate symmetric matrices contains every irreducible representation
(Gow; Kawanaka--Matsuyama; import, not re-read).  Which cuspidal
representations survive restriction to scale-invariant functions on one orbit
was not verified.

**Twist.**  The Legendre-twisted sector is unitarily equivalent to the
untwisted one, via multiplication by the invariant section `chi(det S)`, and
the runs agree.

| pair | norm | excess |
|---|---|---|
| arithmetic `m = 19` | 3.474110 | +0.010009 |
| random | 3.465651 | +0.001549 |

The arithmetic value `lmin = -3.474110` equals, to six digits, the Legendre
`P^2` sector at `p = 29` from batch 1.  So the largest eigenvalue here lies in
a degenerate-series constituent of dimension `p^2+p+1 = 871`.  That excess is
the small-`p` fluctuation, which disappears at larger `p` in the `P^2` table.
No larger eigenvalue from any other constituent was detected (`k = 300`).

## Interpretation

- In three sectors the congruence Schreier spectra of this certified thin free
  subgroup show no outlier above the regular norm beyond about `2e-4` at
  `N ~ 1e6`, for three weightings, apart from the finite-order transient: the
  degenerate principal series (both twists), and the principal series
  including Steinberg (checked for one weighting only).  In these sectors they
  are indistinguishable from Haar-random pairs.
- So there is no small-representation obstruction in the degenerate series at
  this scale.  That series is the most structured sector and the natural place
  for an arithmetic outlier.  It is weak evidence for
  `cubic-division-congruence-representations-converge-strongly` in these
  sectors.  It says nothing about cuspidal sectors, other group-ring elements,
  or the asymptotic limit.

## Reproduction (MSI, gcc 8.5, `-O2 -std=gnu99 -lm`)

- `experiments/cubic-division-sc/sc_p2.c` together with `sc_p2_main.c` builds `sc`:
  - `sc search 1` finds the norm-one elements;
  - `sc pingpong 0 1 -1 0 -1 -1 -1 -1 -1 60` gives the freeness certificate;
  - `sc schreier p <9 coeffs> m twist ctl 600 p` runs one `P^2` computation.
- `sc_p2.c` together with `sc_flags.c` builds `scf`: `scf run p <9 coeffs> m space ctl c1 c2 600 p`.
- Raw output: `res1-p2.txt` (432 runs), `res2-flags-weighted.txt` (243 runs),
  `search1.txt`.
