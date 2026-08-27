---
rg: 2
id: fano-unsafe-support-compresses-to-a-full-nand-packet
kind: claim
title: Every Fano-unsafe local support contains a full three-of-four Boolean packet
distinct_from:
  rstar-fano-ghost-affine-hull-criterion: that detects unsafety by a Fano line; this identifies the exact three-atom Boolean nonlinear packet carried by that line.
  binary-tracial-two-csp-has-classical-solution: that proves a whole Boolean unary-binary tracial instance is classical; this is a context-local compression and explicitly does not create a global binary gap source.
  tracial-cap-menus-are-central-core-partitions: that classifies global tracial branch selection; this projection is only a local context carrier and need not reduce the other contexts.
---

**ESTABLISHED LOCAL DICHOTOMY.**  Let `S subseteq V\{0}` be the positive
support of one translated `R_*` context.  If `S` is not a Fano cap, choose a
line

```text
L={u,v,u+v} subseteq S.                                 (FUN1)
```

There are linear functionals `alpha,beta in V^*` with

```text
(alpha(u),beta(u))=(1,0),
(alpha(v),beta(v))=(0,1),
(alpha(u+v),beta(u+v))=(1,1).                           (FUN2)
```

If `P_t` are the context atoms and `E_L=P_u+P_v+P_(u+v)`, the two parity
observables restricted to `E_L` therefore have joint support exactly

```text
{10,01,11}=F_2^2\{00}.                                 (FUN3)
```

Every one of the three atoms is nonzero (and has positive faithful trace),
so this is the full minimal nonlinear/NAND packet, not a proper affine
subsupport.

Thus every local support satisfies a sharp alternative:

```text
cap-supported and affine-safe,
or it contains a full three-of-four Boolean packet.     (FUN4)
```

The second branch is not a solution of the global compiler problem.
`E_L` is a context-local spectral projection and generally neither central
nor reducing for the other context algebras.  Moreover an entire tracial
Boolean unary-binary CSP collapses classically by
`binary-tracial-two-csp-has-classical-solution`.  The dichotomy therefore
localizes the unavoidable nonlinear mass, but still needs the same
common-carrier/interference mechanism to make it load-bearing.
