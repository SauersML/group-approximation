---
rg: 2
id: agent-free-compressor-payload-kernel-fixed-sector
kind: claim
title: Forbidden BCS mass creates a positive-density sector fixed by the free quotient kernel
distinct_from:
  shared-bcs-carrier-localizes-free-compressor-quotient: That additionally decodes the finite parent and child packet actions and a moved parent generator; this asks only for the infinite quotient kernel to fix one positive-density adjoint sector.
  predicate-rank-jump-forces-adjoint-reynolds-gap: That constructs a child-versus-parent finite-packet commutant difference after localization; this stops before the packet comparison because a positive-density finite-quotient sector is already impossible in canonical microstates.
  bcs-atom-detects-its-e5-central-root: That transfers one BCS atom to one coefficient-root spectral support; this requires a sector on which all fixed words in an infinite normal kernel act trivially.
---

**OPEN MINIMAL FREE-COMPRESSOR GATE.**  Use
`finite-inclusion-is-free-self-compressor-quotient` only for its epimorphism

```text
theta:F->B_f
```

and its finite normal generating list `r_1,...,r_s` for the infinite kernel
`N=ker(theta)`.  Construct a finite ordinary group presentation containing
`F` injectively and a nontrivial marked word, with an exact perfect tracial
BCS model, such that every canonical normalized-HS microstate supplies an
adjoint projection `E` satisfying

```text
tr_ad(E)>=c q_bad^2-o(1),                              (PKF1)
||(S(r_j)-1)E||_2=o(1)                 (1<=j<=s),      (PKF2)
||[E,S(x_i)]||_2=o(1)                  (x_i in X),     (PKF3)
```

where `X` is one free basis of `F`, `S(g)=Ad(U(g))`, and `q_bad` is the
robust shared-BCS forbidden mass on the marked carrier.  The constants may
depend on the fixed BCS and quotient, but not on matrix dimension.

Equations `(PKF2)--(PKF3)` imply that every fixed element of `N` acts
trivially on `E`: write it as a fixed product of conjugates of the `r_j` and
apply the adjoint version of `(FQS1c)`.  Robust BCS soundness and mark
separation make the right side of `(PKF1)` bounded below.  Since `N` is
infinite, `canonical-infinite-subgroup-has-zero-adjoint-fixed-density` then
gives the contradiction directly.

This target is strictly weaker than the previous localized quotient route.
No action of `F/N=B_f` has to be reconstructed, no child image `A_f` is
needed, and no parent generator has to move the carrier.  It is enough to
conditionally annihilate the finite normal generating rows while keeping
the resulting projection approximately invariant under the free basis.

The exact perfect model is consistent because its forbidden mass is zero,
so `(PKF1)` is allowed to return the zero projection.  The remaining problem
is therefore one payload-conditional fixed-space construction, not the
finite packet rank comparison or the one-sided self-copy endpoint.

## Attempts

- Finite packet and quotient-covariance relations alone do not prove
  `(PKF2)`: an independent representation of the free kernel can remain on a
  multiplicity factor while the finite quotient table is exact.
- Root-support decoding supplies a carrier but has not removed that kernel
  multiplicity.  A successful relation must therefore couple the payload to
  the actual kernel units, not merely to their finite-quotient action on a
  root packet.
- Even exact named packet covariance leaves a canonical vanishing-density
  kernel gauge.  `packet-covariant-kernel-gauge` writes each free generator as
  `pi(theta(x_i)) tensor W_i`; on the quotient kernel only `W` remains.  In
  finite regular quotients the normalized kernel-fixed adjoint density is
  exactly `1/|q_k(N)| -> 0`, while the outer forbidden Reynolds gap and all
  named covariance rows remain exact.  Thus the missing payload rows must
  force a uniform positive commutant-density law for the multiplicity action;
  matching the finite packet automorphism is not enough.
