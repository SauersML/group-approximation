---
rg: 2
id: profile-itinerary-meet-extracts-finite-readable-summand
kind: claim
title: A profile-pure finite orbit is exactly a finite-readable central summand
distinct_from:
  profile-pure-finite-projection-orbit-groupifies-zpc-gap: that compiles the given ambient orbit directly; this replaces it by an intrinsic projection in the readable translate algebra and identifies the exact central summand it detects.
  factorial-profile-pure-orbit-forces-finite-readable-translates: that assumes the orbit projection lies in a factorial generated algebra and makes an orbit sum scalar; this needs neither assumption and first takes the full readable itinerary meet.
  ergodic-profile-pure-finite-orbit-implies-finite-readable: that is a measure-theoretic ergodic statement for a set in the readable algebra; this starts with an arbitrary projection in an ambient finite algebra and proves an operator-algebraic central-summand equivalence.
---

Let `(M,tau,pi)` be a faithful finite tracial representation in the negative
corner of a controlled ZPC model. Put

```text
N=W*(D_0,pi(Q_G)),
D_infinity=W*(pi(g)D_0pi(g)^*:g in Q_G),
```

and assume `D_infinity` is abelian. The following are equivalent.

1. There is a nonzero projection `p_0 in M`, not assumed to lie in `N`, whose
   `Q_G`-conjugacy orbit is finite and whose every orbit point lies below one
   atom of `D_0`.
2. There is such a projection `q_0` inside `D_infinity`.
3. There is a nonzero central projection `z in Z(N)` such that
   `D_infinity z` is finite dimensional.

The implication from 1 to 2 is canonical: if `H` stabilizes `p_0` and
`r(gH)` is the unique readable profile containing
`pi(g)p_0pi(g)^*`, then

```text
q_0=meet_(g in Q_G) pi(g)^* E_(r(gH)) pi(g)            (PIC1)
```

is nonzero, belongs to `D_infinity`, is fixed by `H`, and has the same
profile itinerary. For 2 to 3 one may take

```text
z=join_(g in Q_G) pi(g)q_0pi(g)^*.                     (PIC2)
```

Compression by `z` preserves every exact controlled relation and every
zero-loss identity, and the normalized compressed trace is faithful.
Consequently, for a fixed finite game, existence of a perfect tracial model
with any finite profile-pure orbit is equivalent to existence of a perfect
tracial model with finite-dimensional readable translate algebra, and also
to existence of a factorial such model after central decomposition. If
`omega*(G)<1`, every one of these perfect components is
non-Connes-embeddable. No assertion is made that central compression or
factorial decomposition preserves stabilizer-character/IRS provenance.
