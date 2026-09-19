---
rg: 2
id: core-expectation-misses-exact-endpoint-zero-modes
kind: claim
title: Core-commutant expectation discards genuine exact endpoint zero modes
distinct_from:
  p3-exact-iwahori-endpoints-refute-arbitrary-baseline-alignment: that produces two exact same-core endpoints whose relative gauge does not commute with the root; this converts it into an exact obstruction to the proposed conditional-expectation decomposition.
  congruence-endpoint-orbits-are-restriction-ring-fibers: that classifies the adaptive union of endpoint orbits; this proves no fixed core-commutant linear projection can replace minimization over that union.
  congruence-cross-type-mixing-has-uniform-polar-repair: that averages an intertwiner after two endpoint quotient types have been authenticated; this shows why the analogous averaging is unavailable before that authentication.
---

Let `beta=(R,T)` be the mod-three square-free BS core and let `X_0,X_1`
be the two exact extenders from
`p3-exact-iwahori-endpoints-refute-arbitrary-baseline-alignment`.  Put

```text
c=X_1 X_0,                    E_beta:M_d->beta(K)'.   (CEM1)
```

Both endpoint energies are zero, but `[c,T]!=0`.  Therefore

```text
delta:=||c-E_beta(c)||_2>0.                           (CEM2)
```

After arbitrary amplification, `delta` is unchanged.  Consequently no
dimension-independent estimate, or even qualitative zero-set implication,
of the form

```text
||XX_0-E_beta(XX_0)||_2^2 <= C E_R(X)                (CEM3)
```

can hold for a fixed candidate exact endpoint `X_0`.  Endpoint energy does
not control the part transverse to the full core commutant: that transverse
part contains genuine exact endpoint zero modes.

Replacing the full core commutant by the `R`-commutant does not produce a
uniform route.  The inversion rows control `[XX_0,R]`, but long periodic
BS packets have arbitrarily slow `Ad(R)` modes, so distance to `{R}'` is not
uniformly controlled by that commutator.  Replacing it by the exact endpoint
intertwiner space does work by property `(tau)`, but only after the relevant
finite quotient endpoint types have already been authenticated.

Thus the correct zero set over a core is the nonlinear adaptive union of
endpoint orbits, equivalently the restriction-ring fiber in
`congruence-endpoint-orbits-are-restriction-ring-fibers`.  It is not a
linear subspace or a von Neumann algebra and has no conditional expectation.
A global distance-to-union theorem must select a nearby orbit/type before
using property `(tau)`; decomposing relative to an arbitrary baseline and
then applying same-core gauge coercivity is false even at zero defect.

The nonlinear union is nevertheless metrically explicit after
authentication.  `restriction-fiber-orbits-have-optimal-common-dilation`
cross-adds the unmatched positive and negative irreducible multiplicities
of any two endpoint types.  It merges them into one exact larger endpoint
with optimal added rank `mu d`, while property `(tau)` makes orbit distance
comparable to `sqrt(mu)`.  Hence the mod-three zero modes and every other
exact pair merge at quadratic flexible cost.  This does not select a fiber
for a raw tuple.
