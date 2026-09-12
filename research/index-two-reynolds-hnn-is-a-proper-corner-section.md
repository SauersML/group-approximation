---
rg: 2
id: index-two-reynolds-hnn-is-a-proper-corner-section
kind: claim
title: An index-two Reynolds HNN edge is the canonical proper-corner charged-section geometry
distinct_from:
  subgroup-hecke-hnn-is-a-regular-safe-rank-actuator: That proves the general fixed-space inclusion and its relator estimate; this identifies the unused range complement exactly with the transported index-two atom and matches the charged-section interface.
  central-sign-assignment-atom-is-index-two-reynolds-surplus: That identifies the Boolean atom as a Reynolds difference; this constructs the partial isometry whose final-support complement is that difference.
  proper-corner-charged-section: That still asks for a payload-tied raw phase return and its square clause; this closes the proper-corner support geometry before that phase incidence is added.
---

**ESTABLISHED.**  Let `H<C` have index two and form the HNN extension

```text
Gamma=<B,u | u^(-1) h u=phi(h), h in H>,
```

where `phi:H->C` is injective.  In any unitary representation put

```text
p=e_C,                 q=e_H,                 v=q u p.
```

Then `p<=q`, `q-p=e_H-e_C` is a projection, and the HNN relations give

```text
v=u p,                 v^*v=p,
vv^*=u p u^*<=q.                                      (RPS1)
```

Consequently the unused target support

```text
E_exit=q-vv^*                                           (RPS2)
```

is a projection and, in every finite tracial representation,

```text
tau(E_exit)=tau(q)-tau(p)=tau(e_H-e_C).                 (RPS3)
```

Thus `v` is a source-full one-sided section and its unused branch has exactly
the represented Reynolds-surplus mass.  It is not a full-carrier Morita
equivalence, and external amplification cannot alter `(RPS3)`.  Notice that
`[C:H]=2` makes `e_H-e_C` a projection, but it does **not** imply
`tau(e_H)=2tau(e_C)` in an arbitrary representation.  On a regular packet
summand one additionally has `tau(E_exit)=tau(p)`, but the identity used
below is the representation-uniform `tau(E_exit)=tau(e_H-e_C)`.

For the central-sign assignment pair

```text
H=H_a=<x_i J^(a_i)>,             C=<H_a,J>,
```

`central-sign-assignment-atom-is-index-two-reynolds-surplus` identifies

```text
e_H-e_C=e_H(1-J)/2=A_a.                               (RPS4)
```

Hence the complement of the HNN section has exactly the forbidden
assignment mass:

```text
tau(E_exit)=tau(A_a).                                  (RPS5)
```

This is also dimension-independently robust.  After fixed-finite-group
exactification, `subgroup-hecke-hnn-is-a-regular-safe-rank-actuator` gives

```text
||(1-q)up||_2^2
 <= |H|^(-1) sum_(h in H)
      ||u^* pi(h)u-pi(phi(h))||_2^2.                   (RPS6)
```

Replacing `v` by `qup`, polar-correcting on the source support, and using
trace cyclicity changes `(RPS3)--(RPS5)` only by a fixed constant times the
square root of the displayed relator energy.  No ambient-dimension constant
occurs.

## Exact boundary

This closes the support/rank half of `proper-corner-charged-section`.  It
does **not** yet expose the raw Schur phase required by
`central-square-orients-transverse-ledger`.  The word `u` is a section from
`p` to `vv^*`; its compression to `p` is not a unitary loop, so a global
relation `u^2=J` does not become the required corner equation.  A second
return must carry the same final support and a payload-determined relative
phase, or an ordinary relator must directly authenticate the charged corner
square without completing `p` and its sibling to a full Morita `M_2`.

Accordingly the remaining incidence statement is exactly
`reynolds-proper-section-carries-payload-raw-lift`: couple the section
`(RPS1)` to a source-unitary raw lift `W` on `p`, with `W^2=Jp`, while
retaining the complement `(RPS2)`.  The proper-corner geometry and its
positive exit payment are no longer part of that open assertion.
