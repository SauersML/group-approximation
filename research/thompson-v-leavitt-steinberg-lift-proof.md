---
rg: 2
id: thompson-v-leavitt-steinberg-lift-proof
kind: route
title: Split the restricted central K2 extension using the acyclicity of V
target: thompson-v-lifts-through-binary-leavitt-steinberg-cover
requires:
  - thompson-v-central-extensions-split
  - leavitt-cylinder-swaps-generate-thompson-in-el
  - leavitt-gl-equals-el-and-perfect-unit-group
---

Fix `n>=5`.  Let `j:V->E_n(R)` be the composite of the faithful cylinder-swap
map `V->R^x`, the upper-left block map `R^x->GL_n(R)`, and
`GL_n(R)=E_n(R)`.  The block map is faithful, hence so is `j`.

Set `E=pi_n^(-1)(j(V))`.  In rank at least five the kernel of the Steinberg
projection is central.  Therefore

```text
1 -> ker(pi_n) -> E -> j(V) -> 1                       (1)
```

is a central extension; replacing the kernel in `(1)` by its actual
intersection with `E` if necessary changes nothing.  It is abelian and has
trivial `V`-action.  By `thompson-v-central-extensions-split`, `(1)` has a
unique homomorphic splitting `s:j(V)->E`.  Put `iota_n=s o j`.  Then
`pi_n o iota_n=j`, and injectivity follows immediately from injectivity of
`j`.  Since `n` was arbitrary, this works at every rank `n>=5`.

Because `iota_n` is a homomorphism, all finite symmetric and alternating packet
relations holding in the cylinder-swap subgroup hold exactly upstairs.  The
argument uses only centrality of the Steinberg kernel, not its vanishing or
stable identification with algebraic `K_2(R)`.
