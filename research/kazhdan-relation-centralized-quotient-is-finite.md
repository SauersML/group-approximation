---
rg: 2
id: kazhdan-relation-centralized-quotient-is-finite
kind: claim
title: Centralizing a finite-quotient relation kernel of a Kazhdan group makes the whole quotient finite
distinct_from:
  centralized-quotient-shadow-density-dichotomy: that gives a canonical-trace zero-density-or-finite-base dichotomy for an arbitrary finitely generated source; this proves that the infinite-kernel branch is algebraically impossible as soon as the source is Kazhdan.
  fixed-finite-quotient-adjoint-walls-are-canonical-trace-null: that is a matrix-profile density estimate for a fixed quotient wall; this eliminates the proposed Kazhdan relation-centralized carrier before matrix models are considered.
---

Let `F` have property `(T)`, let `N normal F`, and suppose

```text
B=F/N
```

is finite.  Centralize the relation kernel:

```text
E=F/[F,N],                 A=N/[F,N]<=Z(E).             (KRC1)
```

Then

```text
E/A ~= B,                  [E:A]=|B|<infinity.          (KRC2)
```

Property `(T)` passes from `F` to its quotient `E`, and from `E` to the
finite-index subgroup `A`.  But `A` is abelian by `(KRC1)`, and an abelian
property-`(T)` group is finite.  Hence `A` is finite, and `(KRC2)` gives

```text
|E|=|A||B|<infinity.                                  (KRC3)
```

Consequently this construction cannot combine all three desired features:

1. a Kazhdan source;
2. an exact adjoint shadow of a prescribed finite quotient obtained by
   centralizing its relation kernel; and
3. a proper injective self-compression surviving in the shadow.

Indeed every injective endomorphism of the finite group `E` is surjective.
There is no proper parent/child inclusion left for a Kazhdan spectral gap to
transport.  Thus property `(T)` does not repair the density loss in
`centralized-quotient-shadow-density-dichotomy`; it collapses the only
algebraic branch in which the central-character carrier could have remained
macroscopic.
