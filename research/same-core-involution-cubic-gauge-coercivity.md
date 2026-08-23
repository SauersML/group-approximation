---
rg: 2
id: same-core-involution-cubic-gauge-coercivity
kind: claim
title: One involution row and one cubic globally coerce every same-core gauge
distinct_from:
  iwahori-uniform-infinitesimal-rigidity: that is a differential estimate for the whole compatibility map; this is an exact global nonlinear identity for changing only the extending involution over one exact extendable BS core.
  iwahori-cubics-control-aggregate-weighted-bs-orbit-energy: that asks for a Koopman inverse estimate before an exact extending core has been authenticated; this shows no spectral estimate is needed after such a core is available.
  sign-plateau-involution-split-or-pay: that treats sign gauges by projection rounding without assuming an exact cubic baseline; this handles every unitary gauge and uses the exact baseline cubic.
---

Let `x_0,t` be unitaries with

```text
x_0^2=1,       (x_0 t)^3=1.                           (SCG1)
```

Let `c` be any unitary commuting with `t`, and put `x=c x_0`.  Then

```text
||c-1||_2
 <= ||x^2-1||_2+||(x t)^3-1||_2.                     (SCG2)
```

The estimate is exact, dimension-free, and global: `c` need not be close
to one in operator norm or normalized HS norm.  Hence every correction
gauge lying in the `t` commutant is paid by just the involution row and the
first cubic once an exact extending involution `x_0` over the same core has
been identified.

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
   escapes around an exact extendable core.
2. No normalized-HS Taylor theorem, polar functional calculus, aggregate
   Carleson estimate, or opposite-root trace orthogonality is needed in that
   basin.
3. The surviving global theorem is basin capture/authentication: flexibly
   perturb the exactified BS core to one admitting an exact `x_0` near the
   approximate involution.  This is the same noncongruence content as
   `regular-iwahori-relative-congruence-exactification` and
   `iwahori-outlier-repair`.
4. In square-free coordinates, the terminal analytic interface is exactly:
   authenticate one extending endpoint on the same `(r,t)` core, then use
   the second cubic to promote the automatically `r`-central relative gauge
   into `{t}'`.  There is no root-selection or low-Koopman-mode step after
   that promotion.

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
