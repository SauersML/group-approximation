---
rg: 2
id: code-riesz-inverse-is-averaged-first-split
kind: claim
title: The code Riesz inverse is an average of first-splitting martingale masks
distinct_from:
  complete-overlay-row-newton-is-a-code-riesz-multiplier: that identifies the assembled Schur multiplier; this gives its exact random-prefix representation for every code-character subset
  junge-riesz-bmo-does-not-close-code-newton: that audits endpoint estimates and common cuts; this establishes only the algebraic martingale identity
---

At an exact code-character decomposition, fix distinct characters `chi,psi`,
put `z=chi+psi`, and let `S=supp(z)`.  If `pi` is a uniform permutation of
the `L` coordinates and `J_pi(z)` is the first element of `S` in `pi` order,
then

```text
(1/|S|)sum_(j in S)b_(i,j)
   =E_pi b_(i,J_pi(z)).                                  (RFS1)
```

Indeed every member of `S` is equally likely to be first.  This is exactly
the coefficient average in the character-block inverse `(CRM2)`.

For fixed `pi`, let `E_k^pi` be the conditional expectation which deletes
matrix blocks `(chi,psi)` unless `chi` and `psi` agree on the first `k`
coordinates in `pi` order.  Prefix agreement is an equivalence relation on
any subset `C` of the cube, so these are conditional expectations onto
nested block algebras even when `C` is a proper code.  Then

```text
E_(k-1)^pi-E_k^pi
```

is the Schur projection onto blocks whose first differing coordinate is
`pi(k)`.  After reversing the finite nesting, these are martingale-difference
projections.  Hence `(RFS1)` expresses the support-normalized code inverse as
an average over permutation filtrations of first-splitting masks.

This identity does not itself prove a martingale-transform bound.  For each
output coordinate `i`, the selected input is the two-form entry
`b_(i,pi(k))`, which changes with the difference layer.  Establishing a
uniform vector-valued martingale-transform or paraproduct estimate for this
layer-dependent array remains necessary.
