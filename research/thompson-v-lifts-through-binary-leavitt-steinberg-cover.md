---
rg: 2
id: thompson-v-lifts-through-binary-leavitt-steinberg-cover
kind: claim
title: The binary-Leavitt Thompson subgroup lifts uniquely through every central-rank Steinberg cover
distinct_from:
  thompson-v-central-extensions-split: that proves the abstract cohomological splitting theorem for every central extension of V; this applies it to the concrete Thompson subgroup inside E_20(L_2(F_2)) and produces an exact subgroup of the finitely presented Steinberg group.
  leavitt-cylinder-swaps-generate-thompson-in-el: that embeds cylinder swaps into an elementary prefix group downstairs; this removes the possible K2 obstruction to lifting that whole subgroup upstairs.
  leavitt-whitehead-20x20-compression-cell: that lifts one Whitehead compression word and only proves its transport identity after projection to E_20; this lifts the Thompson subgroup itself and makes no compression claim.
---

Put `R=L_2(F_2)`.  For every `n>=5`, let

```text
pi_n:St_n(R)->>E_n(R)
```

be the standard Steinberg projection.  The cylinder-swap embedding of
Thompson's group `V` in `R^x`, followed by the block embedding
`R^x=GL_1(R)->GL_n(R)=E_n(R)`, has a unique homomorphic lift

```text
iota_n:V->St_n(R),                pi_n o iota_n = block.    (VSL1)
```

The lift is injective.  Consequently every finite prefix permutation packet
in `V`, including all common-pivot Carmichael families of three-cycles, occurs
with its exact orders and multiplication relations inside each finitely
presented group `St_n(R)`, `n>=5`.  No Schur-cover or unstable-`K_2` phase can turn an
edge relation `(u_i u_j)^2=1` into a nontrivial central element.

This is an exact existence theorem, not a bounded-area theorem.  The unique
splitting need not send deep prefix permutations to words whose null loops
have uniformly bounded area in a fixed finite presentation.  The rank-20
instance is singled out because the existing Whitehead compression cell lives
there.  Its quantitative question is isolated in
`leavitt-steinberg-bounded-area-carmichael-lift`.
