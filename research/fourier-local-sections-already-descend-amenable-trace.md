---
rg: 2
id: fourier-local-sections-already-descend-amenable-trace
kind: claim
title: Fourier-word local sections already suffice for amenable-trace descent
distinct_from:
  amenable-trace-descends-through-locally-liftable-quotient: that assumes ucp lifts for every finite-dimensional operator system; this needs them only for the cofinal Fourier word systems of a reduced group algebra.
  binary-leavitt-near-regular-quotient-is-locally-liftable: that asks full local lifting for every singular near cover; this identifies the strictly smaller finite-dimensional lifting surface that would already rule out such a cover.
  leavitt-singular-local-lift-iff-no-witness: that proves the full local-lift terminal has the polarity of witness nonexistence; this proves the same polarity for the weaker Fourier-only terminal and locates the first positive cyclic subclass.
---

**ESTABLISHED WEAK DESCENT CRITERION.**  Let `G` be a discrete group, let

```text
q:A -> C^*_r(G),       tau_A=tau_G o q,                 (FLS1)
```

and assume `tau_A` is amenable.  For a finite self-adjoint set `F subset G`
containing the identity, put

```text
E_F=span{lambda_g:g in F} subset C^*_r(G).              (FLS2)
```

It is enough to assume that every `E_F` admits a ucp section

```text
s_F:E_F -> A,              q s_F=id.                   (FLS3)
```

Under `(FLS3)` the regular trace on `C^*_r(G)` is amenable, and hence `G` is
amenable.  Full LLP or local lifting on arbitrary operator systems is not
needed.

For the binary Leavitt group `Q`, which is nonamenable, every hypothetical
singular free near-state cover therefore fails `(FLS3)` on at least one
finite Fourier word system.  Thus replacing `(BLL2)` by Fourier-only local
sections does not make the universal terminal logically weaker: proving it
for all hypothetical covers already proves witness nonexistence.

There is nevertheless a genuine positive subclass.  In a near cover, if
`g in Q` has infinite order, then the whole cyclic algebra

```text
C^*(lambda_g) ~= C(T)                                  (FLS4)
```

has a unital star-homomorphic section

```text
z |-> pi(g) in A.                                      (FLS5)
```

Indeed `pi(g)` is a unitary and `q(pi(g))=lambda_g`; functional calculus
gives `(FLS5)`.  Consequently every finite operator system contained in one
infinite-cyclic Fourier algebra lifts exactly.  The obstruction must involve
at least two noncommuting word directions or a finite-order spectral
relation; it is not present on isolated generators.

More generally, `equal-difference-gram-averaging-fails-at-four-free-words`
shows that every system contained in one amenable subgroup lifts, by
Choi--Effros nuclear lifting.  For finite subgroups it gives the explicit
positive translation-orbit Gram average.  The same claim also locates the
sharp failure of the tempting extension: averaging entries independently by
equal-difference class is not positive on the free four-word window
`{1,a,b,ba}`, and a global cp Toeplitzizer would force group amenability.

The obvious multiword Gram construction explains the remaining positivity
gate.  For word lifts `v_g=pi(g)`, the matrix

```text
[v_g^* v_h]_(g,h in F) >= 0                           (FLS6)
```

is positive and its quotient is the regular Toeplitz matrix
`[lambda_(g^(-1)h)]`.  Upstairs, however, entries of `(FLS6)` need not agree
when two pairs have the same difference `g^(-1)h`: their discrepancy lies
only in the trace-kernel ideal.  Hence `(FLS6)` does not define a linear map
on `E_(F^(-1)F)`.  Producing a completely positive, collision-consistent
replacement is precisely the finite operator-system problem; trace-null
multiplicative defects do not solve it.

This also exposes the hidden LLP circularity.  An argument which invokes a
generic lifting property of `C^*_r(Q)` on the systems `(FLS2)` has already
supplied enough lifting to make the regular trace amenable, contradicting
the known nonamenability of `Q`.  Any successful proof must use the special
Leavitt relations to rule out the near cover during the construction; it
cannot obtain `(FLS3)` as a harmless preliminary regularity statement.

DERIVATION
fourier-local-amenable-descent-proof
