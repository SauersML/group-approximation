---
rg: 2
id: unnamed-positive-density-fixed-space-is-terminal
kind: claim
title: An unnamed positive-mass approximate fixed contraction already contradicts the canonical character
distinct_from:
  compressed-finite-order-wandering-is-terminal: that uses a named finite-support group-algebra projection and convergence of one localized group-algebra norm; this needs no named carrier and detects its mere dimension by finitely many scalar moments of the wandering word.
  self-similar-cylinder-return-regular-energy-floor: that minimizes the regular displacement of a named projection of fixed trace; this proves a finite-moment obstruction for a model-dependent contraction which need not come from the group algebra or converge to a regular projection.
---

Let `Gamma=<S|R>` be finitely presented.  Suppose there are `alpha>0`, an
integer `N` with `N alpha>1`, and a word `u in Gamma` such that

```text
u^k!=1                         (1<=k<N).              (UFS0)
```

Suppose also that every sufficiently accurate
canonical-trace matrix microstate `U` admits an arbitrary contraction `X_U`
(not required to be a word, a projection, a packet element, or functorially
selected)
with

```text
||X_U||_2^2>=alpha-o(1),
||(u(U)-1)X_U||_2=o(1).                                (UFS1)
```

Then `Gamma` is non-hyperlinear.

More quantitatively, put

```text
B_N(z)=sum_(j=0)^(N-1) z^j,
F_N(z)=N^(-1) B_N(z)^* B_N(z).
```

If `X` is a contraction in `M_d`, `||X||_2^2>=alpha`, and
`||(V-1)X||_2<=epsilon` for a unitary `V`, then

```text
tr(F_N(V))
 >= N (sqrt(alpha)-(N-1)epsilon/2)_+^2.                (UFS2)
```

On the other hand, if

```text
|tr(V^k)|<=eta                 (1<=|k|<N),
```

then

```text
tr(F_N(V))<=1+(N-1)eta.                               (UFS3)
```

Equations `(UFS2)--(UFS3)` are incompatible as `epsilon,eta->0`.  Condition
`(UFS0)` makes the canonical character of every `u^k`, `0<|k|<N`, zero, so
canonical microstates provide exactly the hypothesis of `(UFS3)`.  Infinite
order is sufficient but not necessary: a torsion word of order greater than
`1/alpha` also works by choosing `N` above `1/alpha` and at most that order.

The same conclusion holds for a fixed finite menu `u_1,...,u_r`, provided
the same `alpha,N` work and

```text
u_i^k!=1                 (1<=i<=r, 1<=k<N).           (UFS6)
```

It is enough that every accurate microstate supply `(UFS1)` for **some**
menu entry, which may depend on the microstate.  Along any hypothetical
microstate sequence, one menu index occurs infinitely often; restricting to
that subsequence reduces to the one-word theorem.  Thus finite clause or row
pigeonholing costs no carrier alignment and no density factor beyond the
minimum density already guaranteed for the selected entry.

This removes a load-bearing-looking requirement from localized-return
constructions.  A boundary, groupoid, Toeplitz, or finite-coordinate decoder
does **not** have to identify its returned subspace with a fixed
`q in C[Gamma]`, nor provide a trace-preserving lift of the boundary
diagonal.  It is enough to force the existence of some model-dependent
positive-mass approximate fixed contraction for one word whose first enough
powers remain nontrivial.  In
particular, one need not polar-correct or spectrally threshold a soft carrier
into a projection.  The carrier may wander arbitrarily between matrix models.

The result does not claim that a geometric boundary representation forces
such a contraction in every microstate.  That finite-only mass assertion is
the remaining compiler problem.  It does show that packet alignment and the
regular-trace cylinder energy floor are not additional obligations after an
unnamed mass lower bound has been obtained.
