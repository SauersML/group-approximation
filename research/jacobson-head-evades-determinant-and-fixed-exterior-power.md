---
rg: 2
id: jacobson-head-evades-determinant-and-fixed-exterior-power
kind: claim
title: A balanced Jacobson head evades determinant and every fixed exterior power
artifacts:
  - research/exterior-power-and-determinant-blindness-proof.md
distinct_from:
  scalar-rephased-toeplitz-sections-still-collapse-head: that uses perfectness to control scalar rephasings of a particular finite-section model; this shows that determinant-type invariants cannot control a balanced head in an arbitrary microstate.
  bounded-block-jacobson-microstates-also-collapse: that proves collapse when all irreducible blocks have bounded dimension; exterior powers have rapidly growing dimension and do not reduce to that theorem.
  two-jacobson-commutators-plus-perfectness-have-finite-model: that gives a finite countermodel to a two-word argument; this is an intrinsic blindness statement for determinant and fixed Schur-functor data.
---

**ESTABLISHED.** Let (W_d) be an involution on a complex Hilbert
space of dimension (d=2m), with (m) positive and (m) negative
eigenvalues. This is the spectral profile required by a canonical
trace-zero Jacobson head. Then:

1. after harmless double stabilization, so that (d) is divisible by
   four,

   ```text
   det(W_d)=1
   ```

   while the normalized trace remains zero;

2. the Fuglede--Kadison determinant of (W_d) is one in every finite
   tracial von Neumann algebra, simply because (W_d) is unitary; and

3. for every fixed exterior degree (k), the normalized character is

   ```text
   tr(exterior^k W_d)
     = 0                                      if k is odd,
     = (-1)^j binom(m,j)/binom(2m,2j)         if k=2j.
   ```

   It therefore tends to zero as (d) tends to infinity for every
   fixed positive (k).

Exterior powers also preserve approximate relations with the sharp
dimension-independent-for-fixed-(k) estimate

```text
||exterior^k U-exterior^k V||_2
  <= k ||U-V||_2.                                      (JED1)
```

Consequently, applying any fixed exterior power to a hypothetical
trace-preserving Jacobson microstate produces another approximate
representation whose head still has asymptotically zero trace. It does
not turn that head into the identity. Degrees (k=k(d)) can escape the
fixed-degree character formula only at the cost of the factor (k(d))
in `(JED1)); normalized Hilbert--Schmidt defect tending to zero gives
no such rate.

Thus ordinary determinant, the Fuglede--Kadison determinant of the
unitary head, and fixed exterior powers cannot supply the missing
dimension-free collapse of

```text
x_13(1-ST) in EL_28(F_2<S,T | TS=1>).
```

This is a firewall, not a head-retaining microstate. A successful
obstruction must use the full operator-valued root incidence, rather
than a multiplicative scalar invariant or a fixed-degree functor.

DERIVATION
exterior-power-and-determinant-blindness-proof
