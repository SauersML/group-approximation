---
rg: 2
id: agent-free-compressor-a4-toeplitz-root-compiler
kind: claim
title: One A4 amalgam converts Toeplitz root collapse into a marked involution collapse
distinct_from:
  agent-a4-bridge-transfers-forbidden-mass-but-stops-at-root-kill: That attaches A4 first to a BCS Reynolds involution and then seeks a payload root; this starts from the abstractly nontrivial Toeplitz root and needs no BCS front end.
  agent-free-compressor-bcl-root-is-abstractly-zero: That root cannot be an amalgam edge; the Toeplitz defect root used here has an injected order-three subgroup.
  hs-schur-toeplitz-root-defect-collapse: That is the remaining analytic root-kill theorem; this is the exact Bass--Serre compiler after it.
---

Choose the Toeplitz splitting field in characteristic `3`.  The group and
root of `schur-toeplitz-root-mark-is-fd-invisible` satisfy

```text
H_f=<...>,                 1!=w_f=x_12(P_f),
order(w_f)=3.                                             (ATC1)
```

Write the standard triangle presentation

```text
A4=<b,z | b^2=z^3=(bz)^3=1>,                            (ATC2)
```

and form the single-edge amalgam

```text
G_ATC=A4 *_(<z>=<w_f>) H_f.                             (ATC3)
```

Bass--Serre normal form embeds both factors.  In particular the marked
involution

```text
J_ATC=b                                                   (ATC4)
```

is nontrivial in `G_ATC`.

If the qualitative statement in
`hs-schur-toeplitz-root-defect-collapse` holds, every homomorphism from
`G_ATC` to a tracial matrix ultraproduct kills `J_ATC`.  Indeed it kills
`w_f=z`; then `(ATC2)` gives both `b^2=1` and `b^3=1`, so `b=1`.
Consequently `G_ATC` is nonhyperlinear.  Higman's embedding theorem then
puts it in a finitely presented nonhyperlinear overgroup.

The implication has a dimension-uniform finite-word form.  In any
normalized-HS approximate representation of `(ATC2)--(ATC3)`,

```text
||b-1||_2
 <= C (||w_f-1||_2+sqrt(E_pres)),                       (ATC5)
```

because `z=w_f`, `(bz)^3=1`, and `z` near `1` make `b^3` near `1`, while
`b^2` is near `1`, and `b=b^3(b^2)^(-1)`.  Thus no further carrier,
Reynolds, or BCS-to-root theorem is required after Toeplitz root collapse.

This also answers the injectivity question for a finite mixed relation:
identifying the two genuine `C_3` subgroups is safe and preserves the mark.
What remains open is exactly the native normalized-HS collapse of `w_f`;
the A4 edge supplies no new estimate for it.

This last limitation is exact.  Every unitary `W` with `W^3=1` extends to a
representation of `(ATC2)` by taking `z=W` and `b=1`; this is the
abelianization map `A4->C_3`.  Moreover

```text
Reg(A4) restricted to C_3 =4 Reg(C_3).
```

Thus a canonical uniform `C_3` microstate also extends across the A4 edge
after one fixed amplification.  The finite mixed relation is analytically
conservative: it converts a root collapse once available, but cannot force
that collapse.
