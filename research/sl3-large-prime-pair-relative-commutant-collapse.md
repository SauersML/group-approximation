---
rg: 2
id: sl3-large-prime-pair-relative-commutant-collapse
kind: claim
title: Relative-commutant collapse for the SL3 pair at a prime p at least 11
distinct_from:
  sl3-pair-relative-commutant-route: that is the p = 2 instance, where the Clifford constant c_2 = 2/21 leaves the p-divisible exact sector open; this is the instance at a prime p >= 11, where p-divisible-lambda-exact-mass-vanishes-at-large-primes empties that sector, so the whole Lambda-exact face reduces to the coprime sector.
  sl3-p3-pair-relative-commutant-collapse: that is the p = 3 instance chosen for its metaplectic flux; this is chosen for the opposite reason, that the depth-free Atkin--Lehner bound needs c_p > 3/4, which first holds at p = 11.
  lambda-exact-p-divisible-sector-is-ultra-deep-or-negligible: that is a theorem about one sector; this is the collapse claim itself at a large prime, whose exact face that theorem and its depth-free successor now confine to the coprime sector.
---

Let `p >= 11` be prime, `Lambda = SL_3(Z)`, `Gamma = SL_3(Z[1/p])`,
`h = diag(p, 1, 1/p)`, and

```text
G_p = < Gamma, t | [t, Lambda] = 1 >.
```

Claim `(RC3-p)`: for every hyperlinear approximation of `G_p`, with
`M = prod_U M_(d_n)` the tracial matrix ultraproduct it defines and
`pi : Gamma -> U(M)` the restriction (regular trace),

```text
pi(Lambda)' cap M  =  pi(Gamma)' cap M.                                   (RC3-p)
```

By `hnn-route-is-relative-commutant-collapse` this makes `G_p` a
finitely presented non-hyperlinear group
(`non-hyperlinear-from-sl3-large-prime-collapse`).  Everything in the
`p = 2` lane is prime-generic and instantiates verbatim (co-density by the
congruence subgroup property and strong approximation, Schlichting completion
`PSL_3(Q_p)`, property (T) of `Lambda`); what is specific to `p >= 11` is
the state of the `Lambda`-exact face.

## Why this prime range

`p-divisible-lambda-exact-mass-vanishes-at-large-primes` gives, for a
microstate whose `Lambda`-part is a genuine representation of level
`p^D m'`, the depth-free inequality `(4 c_p - 3)(1 - nu_0) <= 12 epsilon/kappa_0`
with `c_p > 3/4` exactly when `p >= 11`.  So on the `Lambda`-exact face the
`p`-divisible weight is `O(epsilon)`, and `odd-congruence-lambda-exact-sector-collapses`
closes the coprime sector.  Two things remain:

1. **Robustness of the coprime closure** to an `O(epsilon)` `p`-divisible
   admixture (`coprime-sector-collapse-is-robust-to-small-p-admixture`).
2. **The outlier sector**: microstates whose `Lambda`-part is uniformly far
   from every genuine representation.  Under `sl3-z-weakly-ucp-stable`,
   `kazhdan-subgroup-weak-ucp-exactifies-microstates` removes it.

The route `sl3-large-prime-collapse-from-weak-ucp-stability` records the
resulting conditional closure.

## Attempts

- **Exact face.**  Closed up to the robustness lemma by the two theorems
  above; the ultra-deep towers that survive at `p <= 7` do not exist here.
- **Outliers.**  Nothing beyond the reduction to `sl3-z-weakly-ucp-stable`
  is known.  What is established (`infinite-hyperlinear-kazhdan-group-is-not-hs-stable`)
  is that `SL_3(Z)` is not STRICTLY HS-stable; flexible and weak ucp
  stability on regular-type hyperlinear approximations are open, and both
  this route and the earlier thin-subgroup edge
  `non-hyperlinear-from-sl3-z-weak-ucp-stability` hinge on exactly that
  hypothesis, so the goal is one hypothesis away along two independent
  mechanisms.  Note that the
  `Lambda`-exact analysis needs only that the `Lambda`-part be near a
  genuine representation of `SL_3(Z)` (finite image by superrigidity,
  congruence by the congruence subgroup property), which is exactly what
  weak ucp-stability supplies after the Kazhdan averaging of
  `kazhdan-subgroup-weak-ucp-exactifies-microstates`.
