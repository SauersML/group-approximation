---
rg: 2
id: perfect-gap-zpc-has-profile-pure-finite-projection-orbit
kind: claim
title: A perfect gap ZPC witness has one profile-pure finite projection orbit
distinct_from:
  perfect-gap-zpc-has-finite-readable-translate-algebra: that states the same unresolved IRS existence gate globally; this gives a local projection-orbit certificate, and the itinerary-conditioning theorem proves the two formulations equivalent.
  atomic-readable-translate-algebra-groupifies-zpc-gap: that proves an atom is sufficient; this does not initially require the ambient projection to lie in the readable algebra or the orbit projections to be orthogonal.
  zpc-readable-control-freezing-to-lcs: that asks for one invariant branch with a fixed equation menu; this permits a transitive finite orbit with a different readable profile and active menu at every point.
---

One can choose the finite tailored game `G` and the value-one ZPC-IRS
strategy supplied by `perfect-zpc-irs-quantum-gap-game` so that
`omega*(G)<1/2` and, in its faithful stabilizer-character GNS algebra,
there is a nonzero projection

```text
0!=p_0<=q_-                                               (PFP1)
```

whose `Q_G`-conjugacy orbit is finite and such that every conjugate lies
below one joint readable atom of `D_0`.

The ambient conjugate projections need not be orthogonal or minimal. By
`profile-pure-finite-projection-orbit-groupifies-zpc-gap`, this condition
already yields a finitely presented nonhyperlinear group.

## Attempts and boundary

- Finiteness of `D_infinity` implies `(PFP1)` by choosing any atom.
- A single atom of `D_infinity` also suffices by
  `atomic-readable-translate-algebra-groupifies-zpc-gap`, even when a
  diffuse complementary summand remains before central decomposition.
- Taking `p_0=q_-` gives a finite singleton orbit but generally fails
  profile purity. Taking one `D_0` atom gives profile purity only at the
  base point; all unreadable conjugates must still have definite profiles
  and only finitely many distinct values.
- By `profile-itinerary-meet-extracts-finite-readable-summand`, `(PFP1)`
  is equivalent inside the same GNS algebra to a nonzero central projection
  `z` with `D_infinity z` finite-dimensional and abelian. The canonical
  itinerary meet is a minimal central projection of `D_infinity`, so its
  distinct conjugates are automatically orthogonal.
- In the stabilizer-relation realization,
  `readable-itinerary-central-summand-preserves-irs-provenance` writes
  `z=q_-1_U` for a full-action invariant event and conditions the pmp
  action on `U`. The resulting perfect ZPC-IRS witness has finite full
  readable translate algebra. Conversely, an atom of any finite readable
  witness supplies `(PFP1)`.
- Therefore this claim and
  `perfect-gap-zpc-has-finite-readable-translate-algebra` are equivalent
  unresolved IRS source gates, not two different strengths. The present
  form is useful because a single local orbit certificate can be attacked
  before constructing the conditioned witness.
- The compactness proof of the perfect ZPC witness controls every fixed
  finite cylinder but supplies neither recurrence nor a finite orbit for a
  positive projection. The explicit construction
  `remote-bernoulli-padding-destroys-profile-pure-finite-orbits` shows
  that perfectness, a strict gap, ergodicity, factoriality, and bounded
  verifier depth do not formally force `(PFP1)`; fixed-cylinder limits can
  lose it.
- The exact open source target is thus a specially selected perfect
  ZPC-IRS witness with a nonzero finite-readable central summand,
  equivalently a conditioned perfect witness with finite full readable
  closure.
