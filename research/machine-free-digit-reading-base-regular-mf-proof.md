---
rg: 2
id: machine-free-digit-reading-base-regular-mf-proof
kind: route
title: Embed the digit tower in central HNN extensions of an RF envelope
target: machine-free-digit-reading-base-is-regular-mf
requires:
  - mf-positive-controls
  - regular-mf-central-hnn-closure
  - asymmetric-hnn-embeds-in-central-hnn-of-inner-envelope
---

Put

```text
E=<x,t,mu | mu x mu^-1=x^m, [mu,t]=1>.
```

This is `(Z[1/m]*Z) semidirect Z`, where `mu` multiplies `Z[1/m]` by
`m` and fixes the second free factor.  It is residually finite.  Indeed, a
nonzero `mu`-exponent survives in a finite cyclic quotient.  A nontrivial
kernel word uses finitely many nonzero `Z[1/m]` syllables and nonzero integer
syllables; choose cyclic quotients `Z/q` and `Z/r`, with `(q,m)=1`, in which
all of them survive.  The word remains reduced in `C_q*C_r`.  Residual
finiteness of that finitely generated free product gives a finite-index
subgroup excluding it; intersect all subgroups up to that index to obtain a
characteristic finite-index subgroup.  It is invariant under the finite-order
action induced by multiplication by `m` on `C_q`, so the corresponding
finite semidirect quotient separates the original word.

Let `D_0=E*F(b_1,...,b_s,d)`.  It is finitely generated and residually
finite.  Define automorphisms

```text
delta_i(b_j)=b_j,  delta_i(d)=b_i d,
Xi_i=(Ad(x^-i mu) on E) * delta_i.
```

On `F`, `Xi_i` is exactly `phi_i`.  Form

```text
D=D_0 semidirect F(theta_1,...,theta_s),
```

where `theta_i` implements `Xi_i`.  This group is residually finite.  More
generally, if a finitely generated residually finite group `K` is acted on by
a finitely generated free group, then `K semidirect F_r` is residually
finite: an element with nontrivial actor part is separated by a finite
quotient of `F_r`; for a nontrivial `k in K`, take a characteristic
finite-index subgroup excluding `k`, let the free action descend to the
finite quotient, and then quotient its image in the finite automorphism
group.  This gives a finite semidirect quotient retaining `k`.

Hence `D` has the regular finite-quotient models supplied by
`mf-positive-controls`.  Starting from `D`, adjoin letters `z_i` one at a
time with `[z_i,F]=1`.  The claim `regular-mf-central-hnn-closure` preserves
a regular operator-MF realization at every step.  Map

```text
x,t,b_j,d |-> themselves,       a_i |-> theta_i z_i.
```

Because `z_i` centralizes `F` and `theta_i` implements `phi_i`, all defining
relations of `Gamma'` hold.  The iterated Britton argument in
`asymmetric-hnn-embeds-in-central-hnn-of-inner-envelope` shows this map is
injective: a source-reduced multiple-HNN word remains reduced after each
inner implementer is separated from its central stable letter.  Restricting
the ambient regular realization proves the claim.
