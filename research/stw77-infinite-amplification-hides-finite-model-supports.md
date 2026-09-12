---
rg: 2
id: stw77-infinite-amplification-hides-finite-model-supports
kind: claim
title: Infinite amplification removes a finite model obstruction that cannot descend in norm
distinct_from:
  one-sided-fd-models-allow-finite-junk-corners: that exhibits a finite junk block in an accurate zero-colour model; this proves that infinite amplification repairs exactly such a block upstairs while creating a quantitative norm obstruction to returning its central isometries.
  agent-stw77-zero-type-i-weak-closure-obstruction: that rules out two weak-closure reductions abstractly; this gives an explicit type-I amplification and an exact operator-norm descent gap.
  agent-stw77-zero-type-i-proper-support-models: that repairs all minimal supports inside a type-I von Neumann target; this shows why the repaired supports cannot simply be pulled back through an amplified representation.
---

**ESTABLISHED.**  Let `H` be a separable infinite-dimensional Hilbert
space, let `p in B(H)` be rank one, put `q=1-p`, and set

```text
D=Cp direct-sum Cq subset B(H).
```

For the infinite amplification

```text
iota:B(H)->B(H tensor l2),       iota(x)=x tensor 1,
```

there are exact isometries `S_1,S_2` in the relative commutant
`iota(D)'` with

```text
S_i* S_j=delta_(i,j)1.                                   (1)
```

Thus amplification makes both minimal supports of `D` properly infinite
and completely solves the finite-dimensional commutant splitting problem
upstairs.

Downstairs the splitting has a uniform norm gap.  For every pair of
isometries `s_1,s_2 in B(H)` satisfying

```text
s_i* s_j=delta_(i,j)1,
```

one has

```text
max_i norm([s_i,p]) >= 1/sqrt(2).                        (2)
```

Consequently no net of exact orthogonal isometries centralizing
`iota(D)` can descend, even approximately in operator norm, to isometries
centralizing `D`.

The algebra `D` is exactly the kind of finite junk model occurring in
[[one-sided-fd-models-allow-finite-junk-corners]].  Hence embedding a
zero-colour model into a product of bounded-operator algebras or a type-I
infinite amplification automatically erases the finite-support information
which the proper-block clustering problem must decide.  Product/type-I
stability can descend only after the finite blocks have been clustered or
discarded downstairs; amplification itself supplies no such selection.

DERIVATION
[[stw77-infinite-amplification-descent-gap-proof]]
