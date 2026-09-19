---
rg: 2
id: congruence-endpoint-orbits-are-restriction-ring-fibers
kind: claim
title: Congruence endpoint orbits are restriction-ring fibers with the weighted total-variation metric
distinct_from:
  bs14-global-atoms-are-moving-congruence-restrictions: that identifies the union of all extendible core classes while the quotient level moves; this classifies every global endpoint orbit over one fixed core class and quantifies the distance between different orbits.
  congruence-iwahori-endpoint-fiber-contains-core-commutant-orbits: that treats the single regular global character and finds one orbit; this shows that the full endpoint fiber is a disjoint union of such orbits indexed by a nonnegative restriction-ring fiber.
  regular-congruence-endpoint-orbit-has-uniform-selberg-retraction: that retracts two equal-character representations to one orbit; this compares unequal characters and shows their orbit distance is equivalent to representation-type mismatch.
  three-way-cell-semigroups-have-conductor-but-unbounded-charge: that concerns local incidence semigroups and moving lattice charge; this is the exact global representation-ring fiber after a congruence quotient has been authenticated.
---

Let `Q` be an odd finite congruence quotient, let `K` be the image of the
square-free BS core, and fix an exact `K`-representation `beta` on a
`d`-dimensional space.  Write

```text
res:Z[Irr(Q)] -> Z[Irr(K)]                                (ERF1)
```

for restriction.  The core-commutant conjugacy orbits of exact congruence
endpoints over `beta` are in canonical bijection with

```text
F_beta={m in N[Irr(Q)]:res(m)=[beta]}.                    (ERF2)
```

Thus two endpoint types over one core differ by an element of
`ker(res)` in the Grothendieck group, subject only to nonnegativity.  There
is no additional continuous invariant after quotienting by `beta(K)'`.

The classification is quantitative.  For `m,n in F_beta`, define

```text
ov(m,n)=sum_(alpha in Irr(Q)) dim(alpha) min(m_alpha,n_alpha),
mu(m,n)=1-ov(m,n)/d
       =(1/(2d))sum_alpha dim(alpha)|m_alpha-n_alpha|.       (ERF3)
```

Let `O_m,O_n` be the two corresponding endpoint orbits, measured by the
normalized-HS distance of the extending involution after the common core is
identified.  The congruence spectral-gap constant `kappa>0` is independent
of the quotient and gives

```text
kappa sqrt(mu(m,n))
 <=dist_2(O_m,O_n)
 <=2 sqrt(mu(m,n)).                                       (ERF4)
```

The upper estimate aligns the maximal common `Q`-subrepresentation and
uses an arbitrary `K`-intertwiner on the complementary equal restrictions.
The lower estimate applies property `(tau)` to the Hilbert--Schmidt
intertwining representation; a core intertwiner can be close to a global
intertwiner only on the common isotypic carrier of dimension `ov(m,n)`.

Consequently the correct authenticated-core basin is not one endpoint
orbit.  It is the union of the orbits in `(ERF2)`, with its geometry given
by `(ERF4)`.  Flexible repair must choose `m` adaptively from this fiber.
`cuspidal-redistribution-refutes-regular-core-orbit-basin` is the
positive-diameter kernel direction obtained by moving multiplicity among
the equal-Borel-restriction cuspidal irreducibles.

This exact classification does not by itself round an almost endpoint.
As the congruence level moves, the rank and the diameter of `ker(res)` can
grow, and the raw two-cubic residuals must still authenticate a nearby
nonnegative point of some moving fiber.  It does, however, remove a false
analytic objective: kernel directions cost no relation energy and must be
selected, not suppressed.

