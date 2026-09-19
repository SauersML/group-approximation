---
rg: 2
id: same-core-involution-cubic-gauge-coercivity
kind: claim
title: One involution row and one cubic globally coerce relative gauges between arbitrary same-core endpoints
distinct_from:
  iwahori-uniform-infinitesimal-rigidity: that is a differential estimate for the whole compatibility map; this is an exact global finite-difference identity for changing only the extending unitary over one fixed BS core.
  iwahori-cubics-control-aggregate-weighted-bs-orbit-energy: that asks for existence of a row-tame gauge which absorbs the Weyl residual; this proves that any such gauge is automatically small once both of its endpoints have small involution and first-cubic rows.
  sign-plateau-involution-split-or-pay: that treats sign gauges by projection rounding without assuming an exact cubic baseline; this handles every unitary gauge and uses the exact baseline cubic.
---

Let `x_0,t` be arbitrary unitaries, let `c` be a unitary commuting with `t`,
and put `x_1=cx_0`.  Define the relative row increments

```text
u=x_1^2 x_0^(-2),
v=(x_1t)^3(x_0t)^(-3).                                (SCG1)
```

Then the exact pairwise estimate is

```text
||c-1||_2
 <=||u-1||_2+||v-1||_2
 <=||x_1^2-1||_2+||x_0^2-1||_2
   +||(x_1t)^3-1||_2+||(x_0t)^3-1||_2.               (SCG2)
```

The estimate is exact, dimension-free, and global: neither endpoint need
satisfy either row exactly, and `c` need not be close to one in operator norm
or normalized HS norm.  In particular, if `x_0^2=(x_0t)^3=1`, `(SCG2)`
reduces to the original one-endpoint estimate

```text
||c-1||_2<=||x_1^2-1||_2+||(x_1t)^3-1||_2.           (SCG2')
```

More generally, every relative gauge in `{t}'` between two `O(delta)`
endpoints is itself `O(delta)`.  There is no Taylor remainder and no path
integration: `(SCG2)` compares the finite word values directly.

The old half-parabolic application is `t=s^2`; the proof only needs
`[c,s^2]=0`, not `[c,s]=0`.  In the root-free Iwahori presentation of
`iwahori-square-free-bs14-presentation`, `t` is itself the BS root
generator, so no information is lost through a square map.

There is also a free quantitative alignment from the inversion rows.  If
`r` is unitary, `x_0^2=1`, `x_0 r x_0=r^(-1)`, and `c=x x_0` for any
unitary `x`, then

```text
||[c,r]||_2
 <=||x^2-1||_2+||x r x-r^(-1)||_2.                   (SCG6)
```

Hence, after an exact square-free endpoint `(x_0,r,t)` has been
authenticated on the same core, the approximate gauge is automatically in
the `r` commutant up to relator error.  The sole alignment still not supplied
by the presentation rows individually is promotion from this `r`-central
gauge to the `t` commutant.  Once `[c,t]=o(1)` is obtained, `(SCG2)` finishes
globally.

Consequences:

1. The first Fourier-mode and two-jump Koopman packets cannot be nonlinear
   escapes between two row-tame endpoints over the same core.
2. No normalized-HS Taylor theorem, geodesic integration, polar functional
   calculus, aggregate Carleson estimate, or opposite-root trace
   orthogonality is needed once the correction is known to end at another
   row-tame point.
3. The surviving global theorem is row-tame endpoint selection: choose a
   Weyl-coboundary correction whose corrected endpoint still has small
   involution and first-cubic rows.  Exact basin authentication is one
   sufficient way to do this, but `(SCG2)` needs only a second approximate
   endpoint.
4. In square-free coordinates, the terminal analytic interface is exactly:
   promote the correcting gauge into `{t}'` and keep its target endpoint in
   the two-row basin.  Once both hold, there is no root-selection or
   low-Koopman-mode step.

The hypothesis that the relative gauge commute with the **same** `t` is
essential, not a removable coordinate choice.
`relative-first-triangle-rounding-has-an-odd-root-branch-firewall` produces
exact rounded first vertices whose products converge to `S^2` while every
square root stays a constant distance from `S`.  That independently rounded
vertex changed the retained `(R,t)` core: by
`fourth-power-covariance-unfolds-square-root-branches` its implementer `R`
moves a constant distance.  The root-free presentation never performs this
branch-losing step.

There is also an exact endpoint-choice obstruction even after the core is
held fixed.  `p3-exact-iwahori-endpoints-refute-arbitrary-baseline-alignment`
gives two zero-defect extenders over the same mod-three `(r,t)` core whose
relative gauge fails to commute with `t`.  Thus the second cubic cannot
promote the gauge relative to an arbitrary preselected extender.  Basin
capture must choose a nearby exact endpoint in the input's endpoint
component (equivalently, minimize over the exact endpoint fiber) before
`(SCG2)` is applied.
