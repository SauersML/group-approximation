---
rg: 2
id: affine-active-corner-has-faithful-binary-leavitt-envelope
kind: claim
title: The affine active packet has a faithful one-to-two Leavitt corner envelope
distinct_from:
  affine-sign-twist-swaps-active-blocks-but-is-stationary: that computes the only finite affine block permutation and finds spectral radius one; this freely adjoins a genuine one-to-two projective-module branch.
  affine-s3-active-idempotent-toeplitz-envelope: that makes the full active sum the single cokernel of a one-sided inverse; this makes the active corner isomorphic to two copies of itself.
  binary-leavitt-family-lifts-into-unit-corner: that asks for a Leavitt family inside a pre-existing corner of a group algebra; this constructs the universal relative Leavitt envelope and proves the original affine packet embeds in it.
---

Let `S=k[C_aff]` and let `A in Z(S)` be the three-atom active idempotent of
`affine-s3-active-idempotent-toeplitz-envelope`.  Define the relative binary
Leavitt envelope

```text
L_A(S)=S<s_0,s_1,t_0,t_1>/(
  As_i=s_i=s_iA,       At_i=t_i=t_iA,
  t_i s_j=delta_(ij)A,
  s_0t_0+s_1t_1=A).                                      (ALE1)
```

Then:

1. the canonical map `S->L_A(S)` is injective, so `A` remains nonzero;
2. `L_A(S)` is a finitely presented algebra over the finite field `k`;
3. the active projective module satisfies the literal branching law

   ```text
   A L_A(S) ~= A L_A(S) direct_sum A L_A(S);              (ALE2)
   ```

4. every homomorphism from `L_A(S)` to a finite-dimensional `k`-algebra,
   and more generally to a stably finite ring, kills `A`.

For injectivity, take a countable direct sum `V` of the faithful regular
`S`-module.  The range `AV` is countably infinite-dimensional.  Split it as
`AV=W_0 direct_sum W_1` with each `W_i~=AV`; let `s_i` be an isomorphism
`AV->W_i`, let `t_i` be its inverse on `W_i` and zero on the other summands,
and extend all four maps by zero on `(1-A)V`.  These operators satisfy
`(ALE1)` while the original `S`-action stays faithful.

In a finite-dimensional module `H`, the relations identify `AH` with
`AH direct_sum AH`.  Hence

```text
dim_k(AH)=2 dim_k(AH),                                    (ALE3)
```

so `AH=0`.  In a stably finite ring, `(ALE1)` says that `A` is a properly
infinite idempotent unless it is zero, which is impossible.  Thus `(ALE2)`
is the exact one-to-two branch missing from every finite affine endpoint,
while the faithful countable model supplies the properly infinite
completeness representation allowed by
`kleene-completeness-needs-only-a-nontrivial-exact-representation`.

This is an algebraic return transducer, not yet a normalized-HS group
transducer.  The additive last relation in `(ALE1)` must be compiled through
Steinberg root words, and an approximate root model need not decode to an
approximate coefficient module.
