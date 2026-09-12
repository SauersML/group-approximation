---
rg: 2
id: two-generator-universal-whitehead-container-proof
kind: route
title: Compress the universal host across a free Whitehead-contractible HNN edge
target: two-generator-fp-torsion-free-universal-whitehead-container
requires:
  - higher-whitehead-universal-finitely-presented-torsion-free-group
  - whitehead-injective-two-generator-recursive-compression
  - waldhausen-hnn-vertex-higher-whitehead-injectivity
  - waldhausen-free-double-whitehead-space-contractible
  - fournier-facio-group-is-nonsofic
  - local-approximation-properties-are-marked-closed
  - torsion-free-finitely-presented-non-mf
  - mf-positive-controls
---

Let `U` be the fixed finitely presented torsion-free group in
[[higher-whitehead-universal-finitely-presented-torsion-free-group]]. Apply
the construction of
[[whitehead-injective-two-generator-recursive-compression]] to `Q=U`.
Its proof forms

```text
V=U*F(a,b)
```

and then one HNN extension `E=HNN(V;A,B)`, where `A` and `B` are free
groups with displayed free bases. Because `U` is finitely presented, the
elimination argument gives a finite presentation on two generators. The
torsion-order identity in that construction gives

```text
Tord(E)=Tord(U)=empty,
```

so `E` is torsion-free.

The map `U->V` is split by the free-product retraction. In this finite
presentation specialization the edge `A` is finite-rank free. Its whole
Whitehead space is contractible: specialize
[[waldhausen-free-double-whitehead-space-contractible]] to the double
`A *_A A`, which is `A`. Hence
[[waldhausen-hnn-vertex-higher-whitehead-injectivity]] injects every
`Wh_i(V)->Wh_i(E)`. Thus `Wh_i(U)->Wh_i(E)` is injective for every
`i>=0). Composing with the universal embeddings `K->U` proves the
simultaneous assertion for every `K`.

Finally, the finitely presented torsion-free nonsofic group from
[[fournier-facio-group-is-nonsofic]] and a finitely presented torsion-free
non-MF group from [[torsion-free-finitely-presented-non-mf]] both embed in
`U`, hence in `E`. Soficity is inherited by subgroups, and
[[mf-positive-controls]] records the same inheritance for MF groups.
Therefore `E` is neither sofic nor MF. No hyperlinearity conclusion is
being asserted for this overgroup. QED
