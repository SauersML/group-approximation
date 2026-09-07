---
rg: 2
id: finite-order-central-compression-defect-survives-mf
kind: claim
title: A central involutive compression defect can survive in an MF group
distinct_from:
  infinite-cyclic-compression-lamp-mf: that uses diffuse infinite-order lamps and residual-finite slow bumps; this gives an explicit three-generator norm-corona subgroup whose centralizing element and compression defect are both involutions, with the defect represented by minus the identity.
  compression-defect-dies-in-finite-dimensions: that kills compression-centralizer defects in every exact finite-dimensional representation; this exhibits such a defect in a faithful operator-norm asymptotic representation.
  property-t-free-manuscript-results: that asks for a Property-T-free non-MF obstruction; this is an MF counterexample fencing one attempted way to remove the rigidity input.
artifacts:
  - research/finite-order-central-compression-defect-survives-mf-proof.md
  - research/artifacts/property-t-free-compression-and-descent-check.py
---

**ESTABLISHED.** There is a three-generated countable MF group

```text
G=<a,t,c>
```

such that

```text
ord(a)=infinity,       t<a>t^(-1)=<a^2><<a>,
c^2=1,                 [a,c]=1,
d=[tct^(-1),a]
```

is a nonidentity central involution. In the explicit norm-corona embedding,
`d=-I`. Hence the compression-centralizer defect of the infinite cyclic
subgroup `<a>` contains a nontrivial finite normal subgroup which survives
inside an MF group.

The example rules out a direct Property-`(T)`-free replacement of compression
transport based only on proper compression, finite order of the centralizing
element, or central finite order of the resulting defect. The defect is
macroscopic in both operator norm and normalized Hilbert--Schmidt norm, so
torsion reblocking does not remove it.

DERIVATION
finite-order-central-compression-defect-survives-mf-proof
