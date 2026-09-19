---
rg: 2
id: bs12-sharp-pair-twist-coherent-corrections-are-bounded-below
kind: claim
title: On the sharp BS(1,2) test pair (A_s, D), every correction whose conjugator twists an order-3 unitary carrying f_0 near f_(2N/3) is at least about |sin 3s|/2 away, uniformly in N, and the constant 3/2 at small s is attained by Fourier-gauge corrections
distinct_from:
  bs12-trivially-padded-opnorm-correction: that is the open uniform correction statement (equivalently ESS Q3); this is an N-uniform lower bound for one explicit class of corrections of its sharp test family, and leaves the statement open.
  bs12-separated-doubling-spectra-correct-conjugators-unpadded: that corrects the conjugator with the base fixed and shows the fixed-base floor; this bounds corrections whose base moves inside the twist-coherent class, which includes every Fourier gauge of D of any size.
  bs12-identity-padding-is-removable-in-operator-norm: that removes the padding; this concerns the same-dimension problem left after it.
artifacts:
  - experiments/bs12-twist-holonomy-2026-09-17/twist_holonomy.py
  - experiments/bs12-twist-holonomy-2026-09-17/output.txt
---

**ESTABLISHED** by `bs12-sharp-pair-twist-holonomy-proof`. This is a lane proof
(swarm-0917-w15, reframing, not reviewed). It is elementary and claims no priority.

## Setting

`N` is odd and `p` is an odd prime dividing `N`; `L = ord_p(2)`. In the basis `e_j` (`j in Z/N`),
with `w = e^(2 pi i/N)`:

```text
D e_j = w^j e_j,   V e_j = e_(j+1),   W e_j = e_(j 2^-1 mod N),   A_s = W exp(is(V+V^*)).
```

Then `W D W^* = D^2` and `||A_s D A_s^* - D^2|| = O(s/N)`. Put `f_m = N^(-1/2) sum_j w^(-jm) e_j`.
These satisfy `V f_m = w^m f_m`, `D f_m = f_(m-1)`, `W f_m = f_(2m)` and
`A_s f_m = phi(m) f_(2m)`, where `phi(m) = e^(2is cos(2 pi m/N))`.

Define the holonomy along the doubling orbit of `-N/p`:

```text
hol_p(s) = exp(2is * sum_(k=0)^(L-1) cos(2 pi 2^k/p)),      hol_3(s) = e^(-2is),  hol_7(s) = e^(-is).
```

A **twist** for a unitary `C` is a unitary `u` with `u^p = 1` and `C u C^* = u^2`. Its
**coherence defect** is

```text
kappa(u) = min_theta || u f_0 - e^(i theta) f_(-N/p) ||.
```

## Statement

**(A) Twist-holonomy inequality.** For every unitary `C in U(N)` and every twist `u` for `C`,

```text
| e^(2isL) - hol_p(s) |  <=  2L ||C - A_s||  +  2 kappa(u).
```

For `p = 3` this reads `2|sin 3s| <= 4||C - A_s|| + 2 kappa(u)`. No exactness of any pair is used,
and no bound on `||Z - D||` is used.

**(B) Where twists come from.** If `C Z C^* = Z^2` and `Z^N = 1`, then `u = Z^(N/p)` is a twist
for `C`. Suppose further that `Z = G D G^*` with `G = R h(V)`, where `h: Z/N -> T` is arbitrary
(a Fourier gauge of any size) and `R` is unitary. Then `kappa(u) <= 2||R - 1||`. In particular,
for the whole Fourier-gauge class `Z = h(V) D h(V)^*`, which contains `Z = D`, **every** exact `C`
satisfies

```text
||C - A_s|| >= |sin 3s| / 2        (p = 3, 3 | N),       uniformly in N and in h.
```

For exact pairs with `Z = R h(V) D h(V)^* R^*`, we get `||C - A_s|| + ||R - 1|| >= |sin 3s|/2`.

**(C) Sharpness at small s (computed).** Take the monomial subclass `C = c h(V) W h(V)^*`,
`Z = h(V) D h(V)^*`, and minimize `max(|phase error of C|, |phase step of h|)` by LP.
- The optimum is exactly `1.5 s` for `s in {0.02, 0.1, 0.5}` and `N in {9, 27, 81, 243, 729}`.
- The realized pairs have `||C - A_s|| = ||Z - D|| = 2 sin(0.75 s)`.

Together with (B), the best Fourier-gauge correction has distance `1.5 s + O(s^3)` for every
`N` computed. So `3/2` is the exact small-`s` constant of the twist-coherent class. The lower
bound is proved; the upper bound is computed.

**(D) Other primes.** If `7 | N`, then `2|sin(7s/2)| <= 6||C - A_s|| + 2 kappa(u)`. At
`s = pi/3` the `p = 3` bound is empty, but the Fourier-gauge class is still at least `1/6` away.

## What this kills, and what it says about the census

This kills the class of **twist-coherent corrections** of the sharp family: exact pairs `(C, Z)`
for which some twist `u` for `C` has small `kappa(u)`. The class includes
- the fixed base `Z = D`;
- every Fourier gauge `h(V) D h(V)^*`, far from `1` or not;
- small perturbations `R` of these.

The pieces of the obstruction:
- **Invariant:** an order-3 unitary `u` with `C u C^* = u^2`. This forces `C^2` to commute with `u`.
- **Where it dies:** `u` carries the fixed-point mode `f_0` to the 2-cycle mode `f_(2N/3)`.
  - There `C^2` has diagonal entry about `e^(4is)` at `f_0`, and about `e^(-2is)` at
    `f_(2N/3)`.
  - Since `C^2` commutes with `u`, the two entries must agree up to `2 kappa`.
- **What it upgrades:** the recorded first-order Livsic statement (holonomy `e^(6is)`, valid only
  for gauges near `1`). The new bound is nonlinear, holds for all gauge sizes, and is uniform in `N`.

**Consequence for the census.** Compare with the moved-base exact pairs of the w14 census
(`bs12-twisted-clock-exact-pair-census`, on the bus):
- `d(0.5, 243) = 0.364 < sin(1.5)/2 = 0.4987`;
- `d/s ~ 1.35 < 1.5` at small `s`.

So those pairs lie outside the twist-coherent class. For every twist `u` of their conjugator,
`kappa(u) >= 2|sin 3s| - 4d`, which is at least `0.54` at `s = 1/2`, `N = 243`.

A proof of ESS Q3 on this family must therefore scramble the mod-3 structure of the base at scale
`1/N`. This is consistent, because `||Z^(N/3) - D^(N/3)||` is not controlled by `||Z - D||`.
A refutation must use an invariant that survives that scrambling. No twist-type invariant does.
