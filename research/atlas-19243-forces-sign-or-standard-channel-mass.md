---
rg: 2
id: atlas-19243-forces-sign-or-standard-channel-mass
kind: claim
title: Collision 19243 localizes fixed mass to the sign or standard S3 conjugation channel
distinct_from:
  atlas-packet-forces-two-s3-covariance-energy: that proves a lower bound on two covariance defects; this diagonalizes that energy into the two nontrivial conjugation types and obtains explicit positive-mass alternatives.
  s3-standard-operator-channel-has-fivefold-reduced-gauge: that counts the five reduced sources inside the standard channel; this proves that collision places positive mass in that five-source channel or in the sign channel, without yet selecting the extension-labelled triple.
  atlas-19243-has-continuous-regular-s3-line-holonomy: that constructs the exact sign-branch escape; this proves the dichotomy and uses that escape to show the standard branch cannot be forced by the interior row alone.
  atlas-relative-block-polar-cut-reduction: that turns mass already localized to one admissible relative-unitary block into a polar common cut; this is the preceding relation-sensitive channel localization and exposes the two remaining authentication branches.
---

Let `K=<h_a,h_b>~=S3` be the collision subgroup and view the relative chart
unitary `U` as a unit vector in normalized Hilbert--Schmidt space under
diagonal conjugation by `K`.  Let

```text
U=U_1+U_epsilon+U_sigma,
m_epsilon=||U_epsilon||_2^2,   m_sigma=||U_sigma||_2^2 (CSM1)
```

be its orthogonal central-isotypic decomposition for the three conjugation
types.  For packet defect `delta`, put

```text
gamma(delta)=max(0,(sqrt(2)-L_19243 delta)/16)^2.       (CSM2)
```

Then every finite multiplicity satisfies the explicit alternative

```text
m_epsilon >= gamma(delta)/16
or
m_sigma   >= gamma(delta)/12.                          (CSM3)
```

Consequently every canonical Atlas microstate sequence has, after passing
to a subsequence, either

```text
liminf m_epsilon >= 1/2048
or
liminf m_sigma   >= 1/1536.                            (CSM4)
```

The same statement under direct collision-relation defect
`epsilon_q=||q_19243(U)-1||_2` uses

```text
gamma_q=max(0,(sqrt(2)-epsilon_q)/8)^2,                (CSM5)
```

and gives limiting alternatives `m_epsilon>=1/512` or
`m_sigma>=1/384`.

This is exact relation-sensitive mass localization, not a packet-margin
count.  On the sign representation each generating transposition acts by
`-1`, so its contribution to the two-generator covariance energy is exactly
`8m_epsilon`.  On the standard representation the positive operator

```text
(I-rho_sigma(h_a))^*(I-rho_sigma(h_a))
 +(I-rho_sigma(h_b))^*(I-rho_sigma(h_b))               (CSM6)
```

has eigenvalues `2,6`: the sum of the two reflection matrices has eigenvalues
`1,-1`.  Hence, writing `e(U)` for the two-generator covariance energy,

```text
e(U) <= 8m_epsilon+6m_sigma.                            (CSM7)
```

The established 19243 wall gives `e(U)>=gamma(delta)`.  If both alternatives
in `(CSM3)` failed, the right side of `(CSM7)` would be strictly below
`gamma(delta)`, a contradiction.  The quotient constants follow identically
from `(CSM5)`.

The standard alternative puts fixed mass in the five-source operator channel
listed by `s3-standard-operator-channel-has-fivefold-reduced-gauge`; a finite
source menu therefore contains one source of mass at least
`gamma(delta)/60`.  This still does not identify the three `S4` extension
coordinates, because those coordinates are not canonically three of the five
operator sources.

The sign alternative is genuine.  In the exact continuous family from
`atlas-19243-has-continuous-regular-s3-line-holonomy`, the relative rotation
acts only on `triv direct_sum sign`, so `m_sigma=0`, while a nonzero angle has
`m_epsilon>0` and collision defect zero.  Therefore no collision-only or
centrality-only inequality can replace `(CSM3)` by a positive lower bound on
the standard channel.

The remaining six-row localization task is now precise: the five saturated
boundary rows must either charge the sign mass and the two unwanted standard
sources, or couple them through one mixed row to the extension-labelled
triple.  Without that boundary transfer, collision supplies a positive typed
channel but not the single admissible incidence carrying
`W,R0,R1,L0,L1`.
