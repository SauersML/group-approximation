# Kun--Thom exterior-return right-module audit

Date: 2026-08-26

## Positive result

For `x=T^*phi(gamma)T`, `z=E_B(x)`, and `y=x-z`, the right kernel `r` of `y`
satisfies

```text
tr(r)<=||z||_2^2<=(q+eta)^2.
```

The kernel of the right-module map `B -> yB` is `eB` with `e<=r`.  Therefore

```text
dim_B(yB)=tr(1-e)>=1-(q+eta)^2.
```

Moreover `yB` lies in `L2(B)^perp`.  A vanished exterior return therefore
creates an asymptotically full orthogonal right edge module.  This sharpens
the earlier quarter-trace support to physical support `1-o(1)`.

## Exact scope firewall

This module dimension does not yield positive normalized adjoint rank.  In an
exact regular quotient block for the Kazhdan subgroup, tensor with one qubit,
take `B=C[Q] tensor 1`, and conjugate a balanced root involution to
`1 tensor Z`.  The returned unitary is orthogonal to `B`, has full support,
and generates a right module of dimension one, but

```text
dim_C(yB)/dim_C L2(M_(2|Q|))=1/(4|Q|)->0.
```

Thus canonical subgroup character and property `(T)` do not promote the
right-module carrier into a positive-density adjoint carrier.  The exact
remaining datum is the left action/strict full-actor compatibility.

No local heavy computation was used.
