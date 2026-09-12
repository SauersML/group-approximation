---
rg: 2
id: stw12-crossed-product-trace-support-proof
kind: route
title: Identify faithful crossed-product traces and apply the UCT AF-embedding theorem
target: stw12-faithful-invariant-trace-af-criterion
requires:
  - tww-gabe-schafhauser-af-embedding-theorem
artifacts:
  - research/artifacts/stw12-faithful-invariant-trace-criterion-audit-2026-08-30.md
---

Put `C=A rtimes_alpha Z`.  Since `A` is AH, it is separable, nuclear, and in
the bootstrap class.  Crossed products by `Z` preserve nuclearity and the
bootstrap class (equivalently here, use the Pimsner--Voiculescu exact
triangle).  Thus `C` is separable, nuclear, exact, and UCT.

The TWW--Gabe--Schafhauser AF-embedding theorem therefore says

```text
C embeds into a unital simple AF algebra
    iff
C has a faithful amenable trace.                               (1)
```

Every trace on the nuclear algebra `C` is amenable, so only faithfulness and
existence remain.

Let `E:C->A` be the canonical faithful conditional expectation.  If `tau`
is an `alpha`-invariant tracial state on `A`, then `tau E` is a tracial state
on `C`.  If `tau` is faithful, so is `tau E`: for `x in C_+ minus {0}`,
faithfulness of `E` gives `E(x)>0`, hence `tau(E(x))>0`.

Conversely, if `rho` is a faithful tracial state on `C`, then its restriction
`tau=rho|_A` is faithful.  Writing `u` for the canonical implementing
unitary,

```text
tau(alpha(a))=rho(u a u*)=rho(a)=tau(a),
```

so `tau` is `alpha`-invariant.  Hence `C` has a faithful trace exactly when
`A` has a faithful invariant trace.  Combining this with (1) proves
`(SFIT)`.

For the simple quasidiagonal corollary, a unital quasidiagonal C-star algebra
has a tracial state: compose its asymptotically multiplicative unital matrix
models with normalized matrix traces and take a weak-star cluster point.
Every tracial state on a simple unital algebra is faithful.  Applying `(SFIT)`
therefore makes a simple quasidiagonal `A rtimes_alpha Z` embeddable into a
unital simple AF algebra, and in particular AF-embeddable.

Nothing in this argument proves the converse for ordinary AF-embeddability.
An embedding into a nonsimple AF algebra need not induce a faithful trace on
the domain; the imported theorem makes the stronger simple-AF target
essential.
