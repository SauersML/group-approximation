---
rg: 2
id: middle-index-marked-heisenberg-whitehead-proof
kind: route
title: Use the middle-coordinate dot-product commutator and the explicit partial-swap conjugations
target: middle-index-marked-heisenberg-packet-is-whitehead-equivariant
requires: []
---

The Leavitt relations give

```text
a_mb_m=s_1(t_(0^m)s_(0^m))t_1=q.                     (1)
```

For `m=n`, the ordinary Steinberg commutator relation applied to
`x_(1,k_m)(a_m)` and `x_(k_m,3)(b_m)` therefore gives `z`.  For `m!=n`,
the middle indices are different, so neither composable root pattern occurs
and the two roots commute.  Roots within either the `X` family or the `Y`
family share one endpoint and commute.  Every root is involutory in
character two.  This proves `(MIH2)`.

Prefix cancellation also gives

```text
a_md_m=a_(m+1),                 c_mb_m=b_(m+1),
c_md_m=s_(0^(m+1))t_(0^(m+1)),
d_mc_m=s_(0^m)t_(0^m).                                  (2)
```

Conjugate `X_m` and `Y_m` successively by the three elementary factors in
`W_m`.  The two additional terms in the first calculation have
coefficients `a_md_m=a_(m+1)` and `a_md_mc_m=a_m`; in characteristic two
the last cancels the original root.  The dual calculation uses
`c_mb_m=b_(m+1)` and `d_mc_mb_m=b_m`.  Hence

```text
W_mX_mW_m^(-1)=X_(m+1),       W_mY_mW_m^(-1)=Y_(m+1). (3)
```

Running the same calculation in reverse swaps the two pairs, and the third
pair has disjoint middle coordinate and is fixed.  All factors of `W_m`
have indices in `{7,8,9}`, so they commute with `z=x_13(q)`.  This proves
`(MIH4)`.

On the `z=-1` sector, the commuting `X_m` have eight joint spectral
projections.  Conjugation by `Y_m` flips exactly the `m`-th sign because of
`(MIH2)`.  The eight projections are therefore unitarily conjugate, so each
has trace `tau(P)/8`; the same matrix-unit calculation identifies the
generated algebra as `M_8(C)` on its label factor.  This proves
`(MIH5)--(MIH6)` without an irreducible-representation classification.

Both constant sign vectors are fixed by the adjacent permutations `(3)`,
so their projections commute with both Whiteheads.  Each compressed
Whitehead is a unitary on `eH`, and direct cancellation of its self-Gram
gives `(MIH7)`.

Finally, on the `M_8` label, `W_1,W_2` implement the two adjacent tensor
factor swaps.  A swap on two qubits has a one-dimensional negative space in
dimension four; after tensoring the untouched qubit its negative fraction
is `2/8=1/4`.  Neither word supplies a one-dimensional negative space in
dimension eight.  Thus the positive Gram is exactly for the Whitehead
transport pair and cannot be relabelled as the required quarter/eighth
selector pair.
