---
rg: 2
id: perfect-gap-zpc-has-profile-pure-finite-projection-orbit
kind: claim
title: A perfect gap ZPC witness has one profile-pure finite projection orbit
distinct_from:
  perfect-gap-zpc-has-finite-readable-translate-algebra: that asks for finiteness of the entire IRS GNS readable algebra; this asks only for a nonzero finite-readable central summand, whose compression need not retain IRS provenance.
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
- By `profile-itinerary-meet-extracts-finite-readable-summand`, `(PFP1)`
  is equivalent inside the same GNS algebra to a nonzero central projection
  `z` with `D_infinity z` finite dimensional. Compressing by `z` gives a
  perfect finite-readable tracial model, and factor decomposition gives a
  factorial one. Thus central variation is only a whole-model distinction,
  not a distinction in tracial existence.
- The remaining difference from
  `perfect-gap-zpc-has-finite-readable-translate-algebra` is provenance:
  central compression and factorial decomposition need not produce another
  stabilizer character or IRS, even though the tracial compiler still
  applies.
- The compactness proof of the perfect ZPC witness controls every fixed
  finite cylinder but supplies neither recurrence nor a finite orbit for a
  positive projection. The explicit construction
  `remote-bernoulli-padding-destroys-profile-pure-finite-orbits` shows that
  perfectness, a strict gap, ergodicity, and bounded verifier depth do not
  formally force `(PFP1)`; fixed-cylinder limits can lose it.
- The exact source target is therefore a nonzero finite-readable central
  summand in the selected IRS GNS model. The compiler may run before
  compression, so the summand itself need not retain IRS provenance.
