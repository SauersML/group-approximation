---
rg: 2
id: sofic-passes-to-subgroups
kind: claim
title: Soficity passes along injective homomorphisms, so nonsoficity passes to overgroups
distinct_from:
  sofic-implies-hyperlinear: that compares two approximation properties of one group, weakening the metric from Hamming to normalized Hilbert-Schmidt; this compares one property across an injection, and neither statement mentions the other's target property.
  hereditary-nonsofic-descent: that is the routed-quotient descent, where a nonsofic simple factor survives in every nontrivial quotient of one specific construction; this is the ambient permanence lemma that descent consumes, with no construction in it.
artifacts:
  - GroupApproximation/Sofic/SoficTransfer.lean
---

ESTABLISHED, kernel-checked. Let `f : H -> G` be an injective group
homomorphism. If `G` is sofic then `H` is sofic. Equivalently, in the
contrapositive form this graph uses,

```text
H <= G and H not sofic   implies   G not sofic.              (SPS1)
```

Soficity is therefore an isomorphism invariant, and nonsoficity is inherited
by every overgroup.

`GroupApproximation/Sofic/SoficTransfer.lean` carries this as
`isSofic_of_injective`, with `isSofic_mulEquiv_iff` for the isomorphism
form. The proof pulls a sofic approximation of `G` back along `f`: the models
are unchanged and the separation condition transfers because `f` is
injective.

The lemma is already consumed inline by `universal-leavitt-el4-nonsofic-proof`,
`d-ary-leavitt-nonsofic-via-binary-corner` and
`hereditary-nonsofic-descent-proof`. It is stated here as its own claim
because `fp-simple-nonsofic-from-boone-higman` needs `(SPS1)` applied to an
envelope that no construction in this graph produces, so the permanence step
can no longer be a line inside somebody else's derivation.

DERIVATION
sofic-passes-to-subgroups-proof
