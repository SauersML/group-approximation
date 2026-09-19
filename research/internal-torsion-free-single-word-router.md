---
rg: 2
id: internal-torsion-free-single-word-router
kind: claim
title: Internally route one torsion-free word onto a two-generated acylindrical quotient
root: true
distinct_from:
  two-generated-single-element-hull-router: that imports Hull--Osin small cancellation as a paper-level black box; this requires the routing construction and its normal-form proof inside the repository, with no literature premise.
  bespoke-routing-lemma: that is tailored to a compression defect and a Property-T partner and currently bottoms out in a cited Greendlinger lemma; this takes an MF-radical word directly and permits no Kazhdan partner.
---

**OPEN INTERNAL ROUTER.**  Given a finitely presented torsion-free
acylindrically hyperbolic group `E`, a nonidentity `d in E`, and a finite
protected set containing `d`, construct in-repository a surjection

```text
q:E->>Q
```

such that `Q` is nontrivial, two-generated, finitely presented, torsion-free,
and acylindrically hyperbolic, `q` is injective on the protected set, and

```text
normalClosure_Q(q(d))=Q.                               (TFR3)
```

No cited small-cancellation theorem may occur as a premise of the final Lean
declaration.  A direct formalization of the needed normal-form/Greendlinger
argument is acceptable; a wrapper around `two-generated-single-element-hull-router`
or `greendlinger-free-product-lemma-citation` is not.
