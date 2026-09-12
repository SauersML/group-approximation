---
rg: 2
id: deligne-sep8-moving-parameter-compression-gap-proof
kind: route
title: Cancel the scalar multiplier in the Hilbert-Schmidt adjoint action
target: deligne-sep8-moving-parameter-compression-gap
requires:
  - sp4-fd-projective-multiplier-is-finite
artifacts:
  - research/artifacts/deligne-sep8-moving-parameter-compression-gap.md
---

For the actual covering cocycle, the finite-cover residual theorem used
in the prerequisite gives the following sharper parameter statement:
an exact finite-dimensional projective representation at parameter `t`
requires `2t=0` in `R/Z`. Indeed it lifts to a representation of
`E_infinity` with `z` acting by `exp(2 pi i t)`. If `z^2` survived, Malcev
residual finiteness of its finitely generated linear image would supply a
finite quotient detecting `z^2`. Writing `M>=3` for the order of the
central image in that quotient, the quotient factors through `E_M` and
detects `z_M^2`, contradicting Deligne's finite residual `2K_M`.

Thus for every parameter in the claim, `pi` has no nonzero
finite-dimensional projective subrepresentation. Its adjoint action

```text
Ad(pi)(g)T=pi(g)T pi(g)^*
```

on Hilbert-Schmidt operators is an ordinary unitary representation of
`Gamma`, since the scalar multiplier cancels. It has no nonzero invariant
vector: an invariant nonzero Hilbert-Schmidt `T` would make the positive
compact operator `T^*T` commute with `pi`; a nonzero spectral projection
of finite rank would be a forbidden finite-dimensional invariant block.

Apply the fixed Kazhdan inequality to the Hilbert-Schmidt vector `P`.
Since `||P||_HS=sqrt(rank P)`, this proves the commutator bound. For a
unitary `U` and finite-rank `P`, a block-matrix calculation gives

```text
||[P,U]||_HS^2=2 Tr(P-(PUP)^*(PUP)).
```

It gives the normalized trace bound in the claim. For the resulting
generator `s`, `||I-A_s^*A_s||_op>=kappa^2/2`. If `V` is any corner
unitary, then `A_s` is a contraction and

```text
||I-A_s^* A_s||_op
  =||V^*V-A_s^*A_s||_op <=2||V-A_s||_op.
```

This yields the operator-norm distance bound. No compactness across
parameters or passage from a tracial approximation to an operator-norm
approximation is used.
