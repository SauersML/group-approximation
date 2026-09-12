---
rg: 2
id: perfect-gap-zpc-has-finite-readable-translate-algebra
kind: claim
title: A perfect gap ZPC witness has a finite full readable translate algebra
distinct_from:
  perfect-zpc-irs-quantum-gap-game: that proves a perfect ZPC-IRS strategy exists on some nonhalting soundness instance but its compactness argument controls only fixed cylinders and gives no bound on the orbit of the readable algebra.
  bcv-halt-readable-finite-orbit-does-not-transfer-to-gap-irs: that locates finite readable orbits in the explicit HALT-side signed-permutation models and explains why they do not automatically transfer to the NONHALT compactness witness; this asks for exactly such a finite orbit after choosing the maximizing gap witness appropriately.
  finite-depth-readable-groupoid-closes-iff-full-orbit-is-finite: that proves finite-depth closure is equivalent to finiteness of the full translate algebra and gives Bernoulli counterexamples for general ZPC actions; this is a special witness-selection assertion for the TailoredMIP gap.
  zpc-readable-control-freezing-to-lcs: that asks for an invariant positive atom and a single frozen LCS branch; finite translate algebra permits a transitive atom orbit and different active menus at different atoms.
---

One can choose the finite tailored game `G` and the value-one ZPC-IRS
strategy supplied by `perfect-zpc-irs-quantum-gap-game` so that, in the
faithful stabilizer-character GNS algebra,

```text
omega*(G)<1/2
```

and the full unreadable translate algebra

```text
D_infinity = W*( pi(g) D_0 pi(g)^* : g in Q_G )
```

of the joint readable spectral algebra `D_0` in the negative central sector
is finite dimensional.

Equivalently, the orbit of `D_0` under all unreadable words is finite, or
there is a finite `Q_G`-invariant Boolean algebra containing `D_0`.  No atom
is required to be invariant: unreadable Pauli variables may permute the
atoms transitively, and the frozen equation menu may change from atom to
atom.  By `finite-readable-translate-algebra-groupifies-zpc-gap`, this is
already sufficient for a finitely presented nonhyperlinear stabilizer
quotient.

## Attempts and boundary

- The explicit BCV HALT-side signed-permutation strategies have this
  property, but the diagonal perfect-gap witness is on the NONHALT branch.
  The present claim is not obtained by importing the HALT strategy.
- Bounded verifier depth gives only the increasing algebras `D_n`; it does
  not make any `D_n` invariant.  A remote Bernoulli shift can make every
  inclusion strict.
- An invariant atom and an orbitwise constant menu are unnecessary.  The
  stabilizer-quotient compiler conjugates the row active at each moving atom
  back to one finite-index stabilizer and kills all of those finitely many
  rows there.
- Magic-square or Pauli selector padding does not refute the claim: such a
  finite selector merely enlarges an already finite atom orbit.  It does
  show that a proof cannot first select a universal frozen branch.
- By `profile-itinerary-meet-extracts-finite-readable-summand` and
  `readable-itinerary-central-summand-preserves-irs-provenance`, this claim is
  equivalent to `perfect-gap-zpc-has-profile-pure-finite-projection-orbit`:
  its local itinerary summand lifts to a full-action invariant event, and
  conditioning on that event gives the finite full readable witness.
- A positive proof could strengthen the pseudo-IRS compactness extraction by
  a uniform bound on the readable translate orbit, or isolate a special
  NONHALT TailoredMIP instance whose readable transition process factors
  through a finite `Q_G`-set.  Neither conclusion follows from the current
  cylinder hierarchy.
