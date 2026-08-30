---
rg: 2
id: profile-itinerary-meet-extracts-finite-readable-summand
kind: claim
title: A profile-pure finite orbit is exactly a finite-readable central summand
distinct_from:
  profile-pure-finite-projection-orbit-groupifies-zpc-gap: that compiles the given ambient orbit directly; this replaces it by an intrinsic orbit and identifies the exact finite-readable central summand it detects.
  factorial-profile-pure-orbit-forces-finite-readable-translates: that assumes the orbit projection lies in a factorial generated algebra and assumes the full readable closure abelian before making an orbit sum scalar; this needs neither assumption and instead proves the itinerary meet is a minimal central readable projection.
  ergodic-profile-pure-finite-orbit-implies-finite-readable: that is a measure-theoretic ergodic statement for a set already in an abelian readable algebra; this starts with an arbitrary ambient projection and derives an abelian finite-dimensional compressed readable algebra.
---

Let `(M,tau,pi)` be a faithful finite tracial representation in the negative
corner of a controlled ZPC model. Put

```text
N=W*(D_0,pi(Q_G)),
D_infinity=W*(pi(g)D_0pi(g)^*:g in Q_G).
```

No commutativity of `D_infinity` is assumed. The following are equivalent.

1. There is a nonzero projection `p_0 in M`, not assumed to lie in `N`,
   whose `Q_G`-conjugacy orbit is finite and whose every orbit point lies
   below one atom of `D_0`.
2. There is such a projection `q_0` inside `D_infinity`.
3. There is a nonzero central projection `z in Z(N)` such that
   `D_infinity z` is finite-dimensional and abelian.

The implication from 1 to 2 is canonical: if `H` stabilizes `p_0` and
`r(gH)` is the unique readable profile containing
`pi(g)p_0pi(g)^*`, then

```text
q_0=meet_(g in Q_G) pi(g)^* E_(r(gH)) pi(g)            (PIC1)
```

is nonzero, belongs to `D_infinity`, is fixed by `H`, and has the same
profile itinerary. In fact it is a minimal central projection of
`D_infinity`. For 2 to 3 take

```text
z=sum_(q in Q_G orbit of q_0) q.                       (PIC2)
```

The distinct orbit points are automatically orthogonal and
`D_infinity z` is their linear span.

Compression by `z` preserves every exact controlled relation and every
zero-loss identity, and the normalized compressed trace is faithful.
Consequently, for a fixed finite game, existence of a perfect tracial model
with any finite profile-pure orbit is equivalent to existence of a perfect
tracial model with finite-dimensional abelian readable translate algebra,
and also to existence of a factorial such model after central decomposition.
If `omega*(G)<1`, every one of these perfect components is
non-Connes-embeddable. No assertion is made here that an arbitrary central
compression or factorial decomposition preserves stabilizer-character/IRS
provenance.
