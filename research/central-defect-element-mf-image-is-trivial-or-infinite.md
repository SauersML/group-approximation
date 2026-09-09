---
rg: 2
id: central-defect-element-mf-image-is-trivial-or-infinite
kind: claim
title: A central element of the compression defect of a Kazhdan subgroup has MF image either trivial or of infinite order
distinct_from:
  normal-kazhdan-defect-non-mf: that kills a normal Kazhdan subgroup of the defect in every corona representation, consumed here; this is the corollary for a central element of infinite order, whose cyclic group is not Kazhdan and is not killed, but whose image can never be a nontrivial torsion element.
  finite-normal-compression-obstruction: that kills a finite normal subgroup of the defect; this concerns an element that may have infinite order in the source and constrains only the order of its image.
  integral-jacobson-defect-has-no-normal-kazhdan-subgroup: that shows the integral defects contain no normal Kazhdan subgroup, so the criterion is silent there; this is what the criterion still says about the infinite cyclic central elements those defects do contain.
artifacts:
  - research/artifacts/jacobson-exact-torsion-radical-and-integral-dichotomy-2026-09-09.md
---

**ESTABLISHED.**  Let `Delta` be countable, let `L <= Delta` have
property (T), and let

```text
zeta in Z(Delta) cap D_Delta(L),                                        (TI1)
```

with `D_Delta(L)` the compression--centralizer defect.  Then for every
homomorphism `phi : Delta -> M` with `M` MF,

```text
phi(zeta) = 1     or     phi(zeta) has infinite order.                  (TI2)
```

No assumption is made on the order of `zeta` itself; the finite
subgroup that the criterion kills occurs in the image, not in `Delta`.

**Use.**  Over the integral Jacobson algebra the manuscript's
four-coordinate central defect element `zeta = diag(1,1,1,1 + f_12)`
generates an infinite cyclic group, so `normal-kazhdan-defect-non-mf`
does not apply to it; `(TI2)` says that any MF image of the ambient
group is either trivial on `zeta` or faithful on `<zeta>`.  This is the
step that turns any nontrivial kernel on `SL_fin(Z)` into total collapse
in `integral-jacobson-mf-radical-is-all-or-nothing`.

Derivation: `central-defect-element-mf-image-is-trivial-or-infinite-proof`.
