---
rg: 2
id: leavitt-presentation-double-fd-radical-is-fold-kernel
kind: claim
title: The finite-dimensional radical of the Leavitt presentation double is exactly its fold kernel
distinct_from:
  simple-map-quotient-has-rigid-fd-restriction: that proves injectivity of restriction for two representations of the free vertex; this computes the finite-dimensional radical of the entire symmetric double and the resulting trace-selection obstruction.
  shulman-symmetric-double-has-no-stable-trace-upgrade: that audits the scope of Shulman's trace theorem for arbitrary symmetric amalgams; this gives an exact candidate-specific theorem saying every honest finite-dimensional representation kills every fold-kernel word.
  common-padding-erases-julia-derivation-density: that dilutes the trace profile of approximate Julia coordinates; this proves that even an exact finite-dimensional replacement, with arbitrary dimension and multiplicity, necessarily loses the whole marked fold kernel.
  leavitt-positive-rank-intertwiner-retention: that asks for genuinely asymptotic almost-quotient sectors; this proves why those sectors cannot be rounded to honest finite-dimensional representations of the double.
---

**ESTABLISHED EXACT-RADICAL OBSTRUCTION.** Let `F` be a finitely generated
free group, let `Q=F/K` be infinite, simple and nonsofic, and form the
symmetric presentation double

```text
P=F *_K F.
```

Let `p:P->F` be the fold map, equal to the identity on both vertex copies.
Then

```text
intersection_(pi:P->U(d), d<infinity) ker(pi)=ker(p).      (PFR1)
```

Indeed, for an exact finite-dimensional representation `pi` of `P`, its two
vertex restrictions `u,v:F->U(d)` agree on `K`.  The restriction-rigidity
theorem `simple-map-quotient-has-rigid-fd-restriction` gives `u=v`, so `pi`
factors through `p`.  This proves that every exact finite-dimensional
representation kills `ker(p)`.  Conversely, if `w notin ker(p)`, the
nontrivial free-group element `p(w)` survives in a finite quotient of `F`;
the corresponding permutation representation composed with `p` separates
`w`.  Hence equality holds in `(PFR1)`.

The same statement holds at the full group C-star level.  If

```text
C*(p):C*(P)->C*(F)
```

is the folded quotient, then

```text
intersection_(Phi:C*(P)->M_d) ker(Phi)=ker(C*(p)).          (PFR1*)
```

The forward inclusion follows from the factorization of every
finite-dimensional group representation.  The reverse inclusion uses that
`C*(F)` is residually finite-dimensional.  Thus the maximal RFD quotient of
Shulman's full symmetric amalgam is exactly the folded vertex algebra
`C*(F)`; none of the extra double direction survives exact matrix
representations.

Consequently every normalized character of an exact finite-dimensional
representation, every convex combination of such characters, and every
pointwise limit of them factors through the fold.  In particular, for
`w in ker(p)`,

```text
tau((u_w-1)^*(u_w-1))=0                               (PFR2)
```

for every trace in the closed finite-dimensional character hull.  But if
`f_0 notin K`, the amalgam normal form makes

```text
w_0=i_0(f_0)i_1(f_0)^(-1)
```

a nontrivial element of `ker(p)`.  Thus no honest finite-dimensional
representation, nor any trace selected by taking limits of honest
finite-dimensional characters, can retain the presentation-double mark.

This is stronger than the padding obstruction on the exactification side:
padding is irrelevant because **every** exact finite-dimensional target,
and indeed every exact matrix representation of the full amalgam, already
factors through the fold.  Therefore a successful
`leavitt-positive-rank-intertwiner-retention` construction must remain
genuinely asymptotic and non-exactifiable at every finite stage.  Shulman's
operator-MF coordinates supply such non-exactness, but select no trace which
sees `(PFR2)`.

DERIVATION
leavitt-presentation-double-fd-radical-proof
