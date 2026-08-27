---
rg: 2
id: depth-one-paired-leavitt-return-enumeration
kind: route
title: Enumerate all depth-one coefficient pairs in exact prefix normal form
target: two-depth-one-leavitt-roots-return-only-constantly
requires:
  - signed-hecke-normalizer-has-eight-external-root-returns
  - one-asymmetric-prefix-cannot-be-signed-hecke-return
  - full-depth-one-leavitt-menu-has-finite-clifford-model
---

Represent a coefficient as a finite `F_2` sum of pairs `(mu,nu)`.  To add
two sums, expand every pair to the maximum domain-prefix length using
`(DPR6)` and cancel equal pairs modulo two.  Multiplication is the exact
prefix rule

```text
(mu,nu)(alpha,beta)=
  (mu gamma,beta)       if alpha=nu gamma,
  (mu,beta gamma)       if nu=alpha gamma,
  0                     otherwise.                    (1)
```

The artifact first verifies `t_is_j=delta_ij` and
`s_0t_0+s_1t_1=1`.  Common-domain prefix replacements give the standard
faithful normal form for these finite sums, so equality with zero or one is
an algebra equality rather than evaluation in a truncated representation.

Build the exact signed character ledger of `L_0` by closing its ten binary
constant generators; it contains `8192` matrices.  For
`g=x_ab(r)x_cd(s)`, use characteristic two to write

```text
g^(-1)=x_cd(s)x_ab(r).
```

Conjugate each signed generator by elementary row and column updates in the
prefix algebra.  The candidate normalizes the signed pair exactly when all
ten conjugates are constant matrices in the ledger with their prescribed
character bits.  Since conjugation is injective and `L_0` is finite,
inclusion on the generators is equality of the pair.

This first finds the `32` exceptional individual normalizers `(DPR3)`, then
tests all `92416` ordered pairs satisfying the two-exit hypothesis.  The
result is `338` constant products and no nonconstant product.  Direct
inspection of those hits gives `(DPR4)`: `304` equal-coefficient
characteristic-two cancellations and the two orders of the complementary
branch-idempotent sum at `17` positions.  The executable assertions check
all counts and assert that no other hit exists.

All enumeration was run through the configured MSI wrapper.  No local
code, computation, build, or Lean compilation was used.
