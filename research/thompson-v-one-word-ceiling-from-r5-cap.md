---
rg: 2
id: thompson-v-one-word-ceiling-from-r5-cap
kind: route
title: Obtain the strict Thompson-V word ceiling from R5 coherent alternating packets
target: thompson-v-one-word-strict-hs-ceiling
requires:
  - thompson-v-r5-coherent-alternating-packet
  - thompson-v-r5-cap-implies-one-word-collapse
---

Apply the conditional collapse theorem to `a=(00 01)`.  It gives

```text
def_R(U)->0  =>  ||U(a)-I||_2->0,
```

which is stronger than the required strict ceiling below the regular value
`2`.  The existing route
`nonhyperlinear-thompson-v-from-one-word-ceiling` then combines this with the
Dudko--Medynets binary CE trace face to prove the root nonhyperlinearity goal.

This route uses the specifically Thompson R5 collision/coherence mechanism;
it is not an invocation of the generic one-word reformulation and is not
available in the affine-clone countermodel, which lacks the globally coherent
R5 swap complex.
