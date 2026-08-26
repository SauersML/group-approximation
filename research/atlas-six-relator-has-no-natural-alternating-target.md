---
rg: 2
id: atlas-six-relator-has-no-natural-alternating-target
kind: claim
title: No two natural eight-point A8 charts satisfy the six Atlas relators in any alternating degree
artifacts:
  - experiments/atlas_six_relator_natural_a13_a16.py
  - experiments/atlas-six-relator-natural-a13-a16.json
distinct_from:
  atlas-six-relator-a12-has-no-marked-pair: that is the exact degree-twelve marking screen; this uses the repeated fixed-point-free letter in s_0 to reduce every larger natural alternating degree back to degree at most twelve.
  atlas-six-relator-natural-orbit-mixing-floor: that says every nontrivial generated component made from natural orbit blocks has degree at least twelve and leaves larger mixed components open; this excludes the entire single-natural-support alternating family in every degree.
  atlas-natural-a8-supports-collapse-before-collision: that uses all twelve cross-A4 packet relations to identify the supports before collision; this uses only s_0 from the six-relator quotient to force at least four points of support overlap.
---

**ESTABLISHED.** Let `Omega` be any finite set and let

```text
alpha,beta:A8 -> Sym(Omega)
```

be marked natural embeddings: each chart has one natural eight-point orbit
and fixes every other point. Then the six equalities

```text
s_0=s_11=s_30=s_44=s_55=c_19243=1                  (NAT1)
```

cannot all hold. Equivalently, no alternating group `A_n`, in any degree,
is a finite-simple six-relator target through two natural-support copies of
`A8`.

The key is already the first word. In its exact free-product normal form,

```text
s_0=x A x C x D,                                     (NAT2)
```

where `x` belongs to the second chart and `A,C,D` to the first. In the
natural eight-point action, the certified exceptional-isomorphism table
gives

```text
x=(1 8)(2 5)(3 6)(4 7),                              (NAT3)
```

up to relabeling. Thus `x` is a fixed-point-free involution.

Let `S_1,S_2` be the two moving supports. If `|S_1 intersect S_2|<=3`, at
most three of the four `x`-pairs meet `S_1`; hence one pair `{p,q}` lies
entirely in `S_2 minus S_1`. The first-chart letters fix both points, and
tracking `(NAT2)` gives

```text
p --x--> q --A--> q --x--> p --C--> p --x--> q --D--> q.
```

Therefore `s_0(p)=q!=p`, contradicting `(NAT1)`. Any survivor must satisfy

```text
|S_1 intersect S_2|>=4,
|S_1 union S_2|<=12.                                 (NAT4)
```

Because the supports overlap and each chart is transitive on its support,
their union is one orbit of the generated group. If its size is at most
eleven, `atlas-six-relator-natural-orbit-mixing-floor` says the component is
pointwise fixed, a contradiction. If its size is twelve, extend by fixed
points if necessary and apply the complete marked-natural `A12` screen
`atlas-six-relator-a12-has-no-marked-pair`. This proves the claim.

The attached exact permutation audit independently checks all `8!` relative
markings at union degrees `13,14,15,16`; every one fails already at `s_0`,
as `(NAT2)--(NAT4)` predict.

