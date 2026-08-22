---
rg: 2
id: existential-fock-library-has-zero-carrier-or-regular-firewall
kind: claim
title: An existential Fock library has a zero-carrier or regular-trace firewall
distinct_from:
  universal-block-return-violates-the-regular-firewall: that rules out one fixed trace-cyclic proper-corner return; this treats a pre-enumerated family of existential row-isometry or no-return gadgets meant to cover all matrix extension types.
  bespoke-extension-nemesis-library-defeats-diagonal-schedules: that proves an exhaustive common-complete extension library would defeat diagonal schedules; this identifies why the literal Fock library does not satisfy its exhaustiveness and completeness hypotheses simultaneously.
  coherent-word-oracles-cannot-branch-on-their-own-tracial-profile: that rules out internal trace-conditioned branching; this audits the proposed existential workaround, which uses no branching.
---

**ESTABLISHED NO-GO for the literal row/Fock construction.**  Consider a
pre-enumerated family of ordinary group extensions whose `M`-th gadget is
intended to expose, on one carrier projection `p`, either

```text
v_i^* v_i=p,   v_i v_i^* pairwise orthogonal,  1<=i<=M,   (EFL1)
```

or a no-return orbit `p_i=u^i p u^{-i}`, `0<=i<M`, of pairwise
orthogonal projections.  The projection and partial isometries may be fixed
matrices over the extended complex group algebra; they may use auxiliary
generators.  For the literal Fock gadget, whose remaining equations admit
the collapsed carrier over every base representation, adjoining all gadgets
to one final group gives the following dichotomy.

1. If the auxiliary carrier is not authenticated, the stipulated collapsed
   assignment gives the zero corner (for a finite-packet idempotent this is
   the collapsed/trivial packet).  Then `(EFL1)` is vacuous and every base
   type has the harmless literal-Fock extension; those equations do not
   cover matrix types.
2. If one fixed algebraic carrier is authenticated and nonzero in the final
   group algebra, apply the left regular representation.  Its faithful finite
   trace gives

   ```text
   M tau(p) <= 1                                            (EFL2)
   ```

   for every `M`.  Hence `tau(p)=0`, so faithfulness gives `p=0`, contrary to
   authentication.  The same computation applies to the no-return orbit.

Thus a common properly infinite representation can realize the desired
Hilbert-hotel geometry only when it is a representation-specific placement,
not a consequence on one fixed positive canonical carrier.  Ordinary group
relations cannot simultaneously force that placement in all finite
extensions while letting the regular representation avoid it.

Using different carriers `p_M` avoids the literal contradiction only by
forcing `tau(p_M)<=1/M`.  Their canonical masses can escape to zero.  To kill
one fixed mark, the construction must additionally prove a finite-prefix
tightness/coverage inequality returning positive mark mass to these carriers.
An infinite join or the assertion “some `p_M` is nonzero” is not one group
relation, and finite direct sums can move their mass beyond every fixed
prefix.

This leaves a precise positive target for existential extension profiles:
not another free Fock tail, but a **canonical tight carrier checksum** or a
genuinely finite-matrix-only localization theorem.  Once such a theorem is
available, `bespoke-extension-nemesis-library-defeats-diagonal-schedules`
does remove every defect-rate issue.

## Attempts

- A common source projection with arbitrarily many orthogonal ranges gives
  the strongest rank explosion, but `(EFL2)` makes it algebraically zero.
- A freely chosen spectral/commutant corner can be zero in every matrix
  extension.  Group equations express compatibility, not existential
  nonzeroness or positive trace.
- A new source at every depth is compatible with the regular trace, but its
  mass bound is `O(1/M)` and has no return to the fixed mark without the
  missing tight checksum.
- Quantum block encoding does not authenticate the source for free.  By
  `grading-zero-corner-does-not-orient-controlled-payload`, a
  Pauli grading can force a zero compression, while every controlled payload
  retains an arbitrary multiplicity orientation.  Selecting and returning
  one orientation is the same missing positive-carrier problem.
