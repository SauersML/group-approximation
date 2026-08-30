---
rg: 2
id: perfect-gap-zpc-has-profile-pure-finite-projection-orbit
kind: claim
title: A perfect gap ZPC witness has one profile-pure finite projection orbit
distinct_from:
  perfect-gap-zpc-has-finite-readable-translate-algebra: that asks for finiteness of the entire full readable translate algebra; this asks only for one nonzero finite-orbit projection and permits nonminimal, overlapping orbit projections and central variation before factorial decomposition.
  atomic-readable-translate-algebra-groupifies-zpc-gap: that proves an atom is sufficient; this does not require the projection to be an atom or the orbit projections to be orthogonal.
  zpc-readable-control-freezing-to-lcs: that asks for one invariant branch with a fixed equation menu; this permits a transitive finite orbit with a different readable profile and active menu at every point.
---

One can choose the finite tailored game `G` and the value-one ZPC-IRS
strategy supplied by `perfect-zpc-irs-quantum-gap-game` so that
`omega*(G)<1/2` and, in its faithful stabilizer-character GNS algebra, there
is a nonzero projection

```text
0!=p_0<=q_-                                               (PFP1)
```

whose `Q_G`-conjugacy orbit is finite and such that every conjugate lies
below one joint readable atom of `D_0`.

The conjugate projections need not be orthogonal or minimal. By
`profile-pure-finite-projection-orbit-groupifies-zpc-gap`, this condition
already yields a finitely presented nonhyperlinear group.

## Attempts and boundary

- Finiteness of `D_infinity` implies `(PFP1)` by choosing any atom.
- A single atom of `D_infinity` also suffices by
  `atomic-readable-translate-algebra-groupifies-zpc-gap`, even when a diffuse
  complementary summand remains before central decomposition.
- Taking `p_0=q_-` gives a finite singleton orbit but generally fails
  profile purity. Taking one `D_0` atom gives profile purity only at the
  base point; all of its unreadable conjugates must still have definite
  profiles and only finitely many distinct values.
- In a factorial negative-corner game algebra, `(PFP1)` already forces
  `D_infinity` finite dimensional. Indeed, the sum of the finite orbit is
  central and hence a positive scalar; its profile slices express each
  `D_0` atom, and after conjugation every readable translate, in the fixed
  finite span of the orbit. Thus the apparent weakening over finite readable
  closure can be strict only through central variation in a nonfactorial
  source.
- The compactness proof of the perfect ZPC witness controls every fixed
  finite cylinder but supplies neither recurrence nor a finite orbit for a
  positive projection. General Bernoulli ZPC actions show that bounded
  verifier depth alone cannot prove `(PFP1)`.
- The exact source target is therefore either a nonfactorial positive
  periodic summand on which the compiler can run directly, or, after
  factorial reduction, the same finite-readable-closure gate already
  isolated by `perfect-gap-zpc-has-finite-readable-translate-algebra`.
