---
rg: 2
id: schur-density-gap-has-no-direct-relator-certificate
kind: claim
title: An embedded Schur density gap cannot be paid by a direct relator-ideal certificate
distinct_from:
  finite-overgroups-cannot-kill-schur-character-density-gap: that constructs a finite-dimensional counterrepresentation for every finite overgroup; this rules out an algebraic certificate in any ambient group where the active selector projection remains nonzero.
  fixed-coefficient-ideal-certificate-controls-hs-defect: that converts a supplied relator-ideal decomposition into HS payment; this proves such a decomposition cannot exist for the Schur density gap itself.
  schur-predicate-is-character-density-difference: that gives the exact group-algebra identity; this applies linear independence in the ambient group algebra to delimit how the identity can be used.
---

Let `Gamma=<S|R>` contain a Schur predicate packet `B_f` in such a way that
the active selector projection

```text
P_f=p_- sum_(x:f(x)=1)p_x
```

is nonzero in `C[Gamma]`. Then the density gap

```text
G_f=Z_(C_f)-Z_(B_f)=P_f/(2D)                         (DRC1)
```

does not belong to the two-sided relator ideal of the presentation inside the
free group algebra. In particular there is no identity

```text
G_f=sum_a lambda_a V_a(r_a-1)W_a                     (DRC2)
```

with `r_a` consequences of the defining group relators.

Therefore `(FDS5)` cannot be proved by a sparse algebraic telescoping
certificate for each local density gap while retaining the nonzero packet
carrier. Its proof must use a principle valid specifically for
finite-dimensional approximate representations: for example property-`(T)`
commutant transport, one-sided compression, stability/integrality, or a
recursive finite-dimensional capacity obstruction.

This does not invalidate `fanizza-schur-density-substitution`. The Fanizza
recurrence residual has a sparse certificate *conditional on* the local gaps.
What is impossible is closing each gap itself by ordinary group-algebra
ideal membership without also killing the exact marked carrier.
