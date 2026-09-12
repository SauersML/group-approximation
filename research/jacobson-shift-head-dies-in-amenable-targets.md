---
rg: 2
id: jacobson-shift-head-dies-in-amenable-targets
kind: claim
title: Every homomorphism of the recursive Jacobson candidate to an amenable group kills its head
distinct_from:
  jacobson-shift-exact-representations-kill-head: that treats exact finite-dimensional unitary representations; this excludes all amenable discrete target groups, including infinite targets.
  finitely-generated-recursive-centralization-is-mf-compatible: that gives an amenable comparison satisfying only recursive centralization and the finite split; this uses the actual normal finitary linear kernel and the nonamenable literal image of the full candidate.
artifacts:
  - research/artifacts/jacobson-recursive-head-dies-in-amenable-targets-2026-09-08.md
---

Every homomorphism from `Gamma=Theta_shift` to an amenable discrete
group kills `w=x_13,Q`, and hence its entire normal closure
`L=GL_fin(F_2^(Z x {1,2,3}))`.

More precisely, let `pi:Gamma->GL(V)` be the literal bilateral action.
Then

```text
C_Gamma(L)=ker(pi).
```

If any group homomorphism `rho` retains `w`, simplicity of `L`
forces `ker(rho) intersect L=1`. Normality then gives

```text
ker(rho)<=C_Gamma(L)=ker(pi),
rho(Gamma) ->> pi(Gamma).
```

The literal image is nonamenable. Its positive-tail Laurent symbol
contains the two matrices `x_12(z)` and `x_12(1)x_21(1)`, which
generate `C_2*C_3` by an explicit fractional-linear ping-pong
argument. This free product contains an index-six free subgroup
of rank two. Thus a head-retaining image cannot be amenable.

This rules out every amenable marked-quotient construction, regardless
of representation type or choice of basis. It does not exclude
nonamenable MF targets or establish the unrestricted matrix gap.

DERIVATION
jacobson-shift-kernel-and-ping-pong-proof
