---
rg: 2
id: fano-empty-link-pruning-proof
kind: route
title: Refine the commuting neighbor PVMs and eliminate every inconsistent joint atom
target: fano-pruning-is-line-hitting-empty-link
requires:
  - commuting-neighborhood-pruning-pays-atom-mass
  - rstar-fano-ghost-affine-hull-criterion
---

Mutual commutation of the neighbor algebras gives the joint PVM

```text
R_boldb=product_(d in N(c)) P_(d,b_d),
sum_boldb R_boldb=1.                                        (FEP1)
```

Exact overlap consistency makes `R_boldb=0` whenever two neighbor
assignments disagree on a shared variable.  If the neighbors are mutually
consistent but some `b_d` disagrees with `a` on `c intersection d`, exact
center--neighbor consistency gives

```text
P_(c,a)R_boldb=0.                                           (FEP2)
```

If `Link(c,a)` is empty, every term in
`P_(c,a)=sum_boldb P_(c,a)R_boldb` vanishes, proving `(FEL1)`.
Finally `(FEL2)` removes at least one point from every Fano line.  The
remaining support is line-free, hence a Fano cap by the established Fano
criterion.

