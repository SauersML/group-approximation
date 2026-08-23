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

Let `x_0,s` be unitaries with

```text
x_0^2=1,       (x_0 s^2)^3=1.                         (SCG1)
```

Let `c` be any unitary commuting with `s`, and put `x=c x_0`.  Then

```text
||c-1||_2
 <= ||x^2-1||_2+||(x s^2)^3-1||_2.                   (SCG2)
```

The estimate is exact, dimension-free, and global: `c` need not be close
to one in operator norm or normalized HS norm.  Hence every correction
gauge lying in the root commutant is paid by just the involution row and the
first cubic once an exact extending involution `x_0` over the same BS core
has been identified.

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

The hypothesis that the relative gauge commute with the **same** root is
essential, not a removable coordinate choice.
`relative-first-triangle-rounding-has-an-odd-root-branch-firewall` produces
exact rounded first vertices whose products converge to `S^2` while every
square root stays a constant distance from `S`.  Its Hadamard rotation is
outside `{S}'`, so `(SCG2)` cannot start an alternating repair from that
independently rounded vertex.
