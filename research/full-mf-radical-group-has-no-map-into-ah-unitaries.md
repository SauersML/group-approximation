---
rg: 2
id: full-mf-radical-group-has-no-map-into-ah-unitaries
kind: claim
title: A full-MF-radical group admits no nontrivial homomorphism into the unitaries of the AH counterexample
distinct_from:
  mf-approximation-does-not-give-k1-injectivity: that says the AH algebra is MF and still fails K_1-injectivity; this draws the consequence for homomorphisms out of a full-MF-radical group and closes an attempted interaction between the two constructions.
  defect-saturation-full-mf-radical: that constructs a group with full MF radical; this says where such a group cannot be represented.
artifacts:
  - research/artifacts/k1-classification-and-extension-bridge-2026-09-07.md
---

Let `H` be a countable group with `Res_MF(H) = H` and let `A` be the AH
algebra of `stw59-simple-ah-non-k1-injective`.  Then

```text
Hom(H, U(A)) = {1}.
```

So the AH counterexample cannot host a non-MF group through a unitary
representation.  This closes one attempted interaction between the two
constructions: the twisted AH obstruction and the compression obstruction
cannot be made to meet inside `U(A)`.
