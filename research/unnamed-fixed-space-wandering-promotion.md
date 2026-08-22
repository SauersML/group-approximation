---
rg: 2
id: unnamed-fixed-space-wandering-promotion
kind: claim
title: Force an unnamed positive-density square-return space for one wandering word
distinct_from:
  localized-square-return-wandering-promotion: that requires the returned carrier to be a fixed nonzero finite-support projection in the group algebra; this permits an arbitrary model-dependent projection and asks only for its density.
  fanizza-coherent-verifier-wandering-promotion: that names the full verifier reflection on a fixed clock and flag packet; this retains neither the verifier payload nor any named packet alignment.
---

**OPEN WEAKER NON--BASS--SERRE PROMOTION TARGET.**  Construct a finitely
presented group `Gamma`, an infinite-order word `w`, and a fixed `alpha>0`
such that every canonical-trace matrix microstate `U` admits some projection
`P_U` satisfying

```text
tr(P_U)>=alpha-o(1),
||(w(U)^2-1)P_U||_2=o(1).                              (UFW1)
```

The projection may depend arbitrarily on the matrix model.  It need not be
the evaluation of a group-algebra projection, a packet Fourier atom, or a
boundary cylinder, and no cross-model coherence is requested.

By `unnamed-positive-density-fixed-space-is-terminal`, `(UFW1)` contradicts
the finitely many canonical scalar moments of `w^2`; hence this target alone
produces a non-hyperlinear group.

This is the surviving finite-multiplicity interface for geometric returns.
A self-similar or groupoid construction may first produce a positive-density
return space in each finite model and allow that space to move with the
model.  The sharp regular-energy floor for a trace-preserving image of one
fixed cylinder is then irrelevant.  What remains genuinely necessary is a
dimension-independent finite-only argument forcing the density lower bound
and the approximate return in **every** canonical microstate.  Merely having
one boundary representation still does not supply `(UFW1)`.

## Attempts

- **Literal boundary-cylinder transport is unnecessary and still fails.**
  Identifying one fixed cylinder with a canonical group-algebra projection is
  blocked by `self-similar-cylinder-return-regular-energy-floor`.  The present
  target deliberately retains only the dimension of the returned space, so
  that obstruction no longer applies to the output.  It does, however, show
  that a trace-preserving boundary lift cannot be the decoder producing it.
- **Finite Bass--Serre models remain dead.**  Their exact finite quotient
  representations reproduce the wandering regular profile and cannot force a
  positive-density fixed space.  Allowing the projection to float does not
  change those countermodels.
- **Deferred live attack.**  Seek a genuinely matrix-coordinate rank theorem
  (for example an orthogonal-exit or finite-multiplicity deficiency) whose
  kernel has density bounded below and on which `w^2-1` is small.  Unlike the
  named-carrier target, no synchronization of that kernel with a fixed packet
  atom is required.
- **One heterogeneous HNN row is sufficient.**
  `hnn-compressed-row-is-unnamed-fixed-carrier` proves that
  `u=a t b^(-1)t^(-1)` fixes the moving carrier `tp` exactly to the extent
  that `a t p` intertwines with `t p b`.  Britton normal form supplies
  infinite order independently.  The live route
  `fanizza-heterogeneous-row-closes-unnamed-return` therefore reduces this
  target to one private/shared compressed row.
