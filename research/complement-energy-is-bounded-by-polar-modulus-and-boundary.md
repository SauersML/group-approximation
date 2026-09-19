---
rg: 2
id: complement-energy-is-bounded-by-polar-modulus-and-boundary
kind: claim
title: Complement energy is bounded by polar error, modulus mismatch, and raw boundary leakage
distinct_from:
  projective-transfer-reduces-to-complement-unitary-extension: that uses a small optimized complement energy to transfer the h-commutator; this gives an explicit upper bound on that optimized energy by testing the identity complement.
  canonical-fold-leak-is-complement-energy-or-h-singularity: that lower-bounds complement energy from the canonical fold leak; this combines with it to force a concrete lattice-boundary or polar-modulus payment.
  leakage-small-polar-compressions-obey-projective-transfer: that uses aggregate generator leakage directly in the final transfer inequality; this separates the additional modulus mismatch created by the block swap.
---

**ESTABLISHED.**  Let `pi:C->U(H)` be an exact representation of a finitely
generated group on `H=PH direct_sum QH`, and put

```text
T_c=Ppi(c)P=rho_c A_c,          A_c=|T_c|,              (CMB1)
```

where `rho_c` is a unitary polar factor (in particular this applies when
`T_c` is invertible).  For `U in U(PH)` define

```text
e_c=||U rho_c-rho_c U||_(2,PH)^2,
mu_c=||U A_c-A_c U||_(2,PH)^2,
ell_c=||Qpi(c)P||_HS^2/rank(P).                         (CMB2)
```

Let `J_C(U)` be the scaled optimized complement energy `(CUE2)`.  Then

```text
J_C(U)<=sum_(c in S_C)(2e_c+2mu_c+8ell_c).              (CMB3)
```

Indeed test the infimum in `J_C` with `Z=I_(QH)` and write
`W=U direct_sum I`.  Relative to `PH direct_sum QH`,

```text
[W,pi(c)] = [[UT_c-T_cU, (U-I)Ppi(c)Q],
             [Qpi(c)P(I-U), 0]].                       (CMB4)
```

For unitary `W,pi(c)`, projective commutator energy is at most
`||[W,pi(c)]||_(2,H)^2`.  The two off-diagonal blocks have squared raw
Hilbert--Schmidt norm at most four times the corresponding leakage norm;
unitarity of `pi(c)` makes the incoming and outgoing leakage traces equal.
After multiplying by `dim(H)/rank(P)`, their total contribution is at most
`8ell_c`.  Finally

```text
UT_c-T_cU=(U rho_c-rho_c U)A_c
           +rho_c(UA_c-A_cU),                          (CMB5)
```

and `||A_c||<=1`; the squared triangle inequality gives the first two terms
of `(CMB3)`.

Apply this to the canonical arithmetic fold profile of
`canonical-fold-leak-is-complement-energy-or-h-singularity`.  If
`|T_h|>=sigma P`, then

```text
(sigma^2/(8K)) E_h
 <= J_C(U)
 <= 2 sum_c e_c+2 sum_c mu_c+8 sum_c ell_c,             (CMB6)
```

where `E_h=1-|tr([U,rho_h])|^2`.  Hence, when the ordinary block-swap
commutator errors `sum_c e_c` tend to zero and canonicality gives
`E_h->1`,

```text
liminf (sum_c mu_c+4 sum_c ell_c)>=sigma^2/(16K).       (CMB7)
```

This is a dimension-free joint boundary payment.  It narrows the arithmetic
terminal to two explicit quantities: the swap fails to preserve the raw
compression moduli on the lattice generators, or a positive aggregate
amount of lattice mass crosses the selected boundary.

It is not yet presentation-energy payment.  Exact flat-singular calibration
models can have positive `ell_c` with zero arithmetic relator defect, and
polar relations do not see `mu_c`.  The missing theorem must use full-double
mixed words to bound these raw quantities by the original normalized-HS
defect, or construct a canonical model in which `(CMB7)` persists.
