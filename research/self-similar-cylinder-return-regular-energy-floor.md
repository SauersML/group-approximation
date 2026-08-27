---
rg: 2
id: self-similar-cylinder-return-regular-energy-floor
kind: claim
title: A self-similar cylinder return has a sharp positive regular-trace energy floor
distinct_from:
  compressed-finite-order-wandering-is-terminal: that only needs nonvanishing of one finite-support regular coefficient; this computes the optimal floor at every prescribed carrier density and applies to arbitrary projections in the regular factor.
  contracting-self-similar-checksum-has-finite-deep-state: that bounds the number of deep section states in a contracting action; this separates the boundary/groupoid trace from the canonical group trace even for noncontracting or infinite-state actions.
  finite-graph-packet-compression-wandering-no-go: that uses finite Bass--Serre normal forms and finite quotients; this applies to prefix-groupoid and inverse-semigroup cylinder returns without any residual-finiteness hypothesis.
---

**ESTABLISHED.** Let `Gamma` be a group, let `w in Gamma` have infinite
order, and put `u=lambda(w^2) in L(Gamma)`.  For every projection `q in
L(Gamma)` of trace `alpha`,

```text
||(u-1)q||_2^2 >= c(alpha)
                  := 2 alpha-(2/pi)sin(pi alpha).       (SCR1)
```

The constant is optimal among all tracial von Neumann algebras containing a
Haar unitary, and is strictly positive for every `alpha>0`.

Consequently an exact self-similar local return cannot be promoted to a
positive canonical carrier merely by importing its cylinder projection.  More
precisely, suppose a prefix-groupoid, inverse-semigroup, Toeplitz, or Leavitt
model contains a diagonal projection `p` and a unitary/full-group element
`v` such that

```text
(v^2-1)p=0,                 tau_boundary(p)=alpha>0.     (SCR2)
```

There is no trace-preserving star homomorphism into `L(Gamma)` which sends
`v` to `lambda(w)` and `p` to a projection, and there is no asymptotic such
lift with carrier traces bounded below by `alpha`: `(SCR1)` gives a fixed
positive defect floor.  This remains true when `(SCR2)` comes from an
infinite-edge or noncontracting prefix table rather than a finite
graph-of-groups packet.

Thus self-similarity does furnish the desired *geometric* phenomenon—an
infinite-order global element can have a finite-order return on a positive
boundary cylinder—but it furnishes it in the wrong trace.  The boundary
diagonal records cylinder measure, whereas the canonical regular trace sees
`lambda(w^2)` as a Haar unitary.  Any route to
`localized-square-return-wandering-promotion` through self-similar normal
forms still needs a genuinely matrix-only trace-promotion step; prefix
refinement, a Toeplitz section, or an inverse-semigroup diagonal embedding is
not that step.

