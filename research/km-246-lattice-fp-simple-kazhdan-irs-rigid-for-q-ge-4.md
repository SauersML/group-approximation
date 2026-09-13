---
rg: 2
id: km-246-lattice-fp-simple-kazhdan-irs-rigid-for-q-ge-4
kind: claim
title: For every prime power q >= 4 the (2,4,6) Kac-Moody lattice modulo its centre is finitely presented, simple, Kazhdan and IRS-rigid
distinct_from:
  simple-kazhdan-kac-moody-lattices-exist: that imports the Caprace--Remy corollary with the general bound q > 1764^n; this pins the type (2,4,6), lowers the bound to q >= 4 from later sources, and adds rigidity of invariant random subgroups.
  caprace-thom-v2-leaves-km-character-rigidity-open: that records what Caprace--Thom v2 does not prove, character rigidity; this records what it does prove for this type, property (T) of the completions at thickness >= 4 and IRS rigidity of the lattice.
---

**ESTABLISHED (literature import).** Let `A` be the generalized Cartan matrix `(KM2)` of
`simple-kazhdan-kac-moody-lattices-exist`, with Weyl group the `(2,4,6)` triangle group,
let `Lambda_q` be the minimal simply connected split Kac--Moody group of type `A` over
`F_q`, and let `Z` be its finite centre. For every prime power `q >= 4` the group

```text
S_q = Lambda_q / Z                                                   (KMQ1)
```

is infinite, finitely presented, simple, has property (T), and every invariant random
subgroup of `S_q` is a convex combination of `delta_e` and `delta_(S_q)`.

**What changes.** The recorded bound `q > 1764^3` came from Dymara--Januszkiewicz through
Caprace--Remy's general corollary. For this type, Kassabov's criterion as applied by
Caprace--Thom gives (T) already at thickness 4. So the smallest member has local rank-two
groups `SL_2(4)^2`, `Sp_4(4)`, `G_2(4)`.

**Why IRS rigidity matters here.** It is the input of
`almost-actions-of-irs-rigid-simple-groups-are-free-or-trivial`: every almost action of
`S_q` that is not asymptotically trivial is, after deleting its global fixed points, a
sofic approximation, so its finite rank-two charts are asymptotically free.

**Not covered.** Character rigidity of `S_q` is open (Caprace--Thom v2, Remark 5.4; see
`caprace-thom-v2-leaves-km-character-rigidity-open`). So no analogous statement for
unitary almost representations follows.

Citation: `km-246-lattice-fp-simple-kazhdan-irs-rigid-for-q-ge-4-citation`.
