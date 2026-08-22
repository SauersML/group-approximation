---
rg: 2
id: unnamed-positive-density-fixed-space-is-terminal
kind: claim
title: An unnamed positive-density approximate fixed space already contradicts the canonical character
distinct_from:
  compressed-finite-order-wandering-is-terminal: that uses a named finite-support group-algebra projection and convergence of one localized group-algebra norm; this needs no named carrier and detects its mere dimension by finitely many scalar moments of the wandering word.
  self-similar-cylinder-return-regular-energy-floor: that minimizes the regular displacement of a named projection of fixed trace; this proves a finite-moment obstruction for a model-dependent projection which need not come from the group algebra or converge to a regular projection.
---

Let `Gamma=<S|R>` be finitely presented and let `u in Gamma` have infinite
order.  Suppose that there is `alpha>0` such that every sufficiently accurate
canonical-trace matrix microstate `U` admits an arbitrary projection `P_U`
(not required to be a word, a packet idempotent, or functorially selected)
with

```text
tr(P_U)>=alpha-o(1),
||(u(U)-1)P_U||_2=o(1).                                (UFS1)
```

Then `Gamma` is non-hyperlinear.

More quantitatively, put

```text
B_N(z)=sum_(j=0)^(N-1) z^j,
F_N(z)=N^(-1) B_N(z)^* B_N(z).
```

If `P` is a projection in `M_d`, `tr(P)>=alpha`, and
`||(V-1)P||_2<=epsilon` for a unitary `V`, then

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

Choose one fixed integer `N` with `N alpha>1`.  Equations `(UFS2)--(UFS3)`
are incompatible as `epsilon,eta->0`.  Since the canonical character of an
infinite-order word has `tau_Gamma(u^k)=0` for every `0<|k|<N`, canonical
microstates provide exactly the hypothesis of `(UFS3)`.

This removes a load-bearing-looking requirement from localized-return
constructions.  A boundary, groupoid, Toeplitz, or finite-coordinate decoder
does **not** have to identify its returned subspace with a fixed
`q in C[Gamma]`, nor provide a trace-preserving lift of the boundary
diagonal.  It is enough to force the existence of some model-dependent
positive-density approximate fixed subspace for one infinite-order word.
The carrier may wander arbitrarily between matrix models.

The result does not claim that a geometric boundary representation forces
such a subspace in every microstate.  That finite-only density assertion is
the remaining compiler problem.  It does show that packet alignment and the
regular-trace cylinder energy floor are not additional obligations after an
unnamed density lower bound has been obtained.

