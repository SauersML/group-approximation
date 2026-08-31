---
rg: 2
id: positive-steinberg-qutrit-bridges-are-central-by-finite
kind: claim
title: Positive Steinberg roots give only central-by-finite qutrit bridges
artifacts:
  - research/positive-steinberg-qutrit-bridge-proof.md
distinct_from:
  finite-positive-root-fragments-have-marked-regular-models: that proves local finiteness for a finite fragment entirely inside a positive unitriangular group; this adds the finite Thompson qutrit actor, tracks all its conjugates, and lifts the resulting finite group through the central Steinberg extension.
  localized-tail-qutrit-wrappers-reflect-hyperlinearity: that closes all off-code actors which stay in localized Thompson copies; this treats genuine elementary roots outside Thompson's group.
  thompson-v-lifts-through-binary-leavitt-steinberg-cover: that embeds the finite packet upstairs and does not add roots; this computes the subgroup generated after finitely many positive roots are added.
---

Let `R=L_(F_2)(1,2)`, let `F` be the order-`3^5` qutrit
prefix packet, and block-embed it by

```text
D(f)=diag(f,1,...,1) in GL_n(R)=EL_n(R).                (PSQ1)
```

Choose any finite set of positive elementary roots

```text
e_(i_alpha,j_alpha)(r_alpha),
                 i_alpha<j_alpha,                      (PSQ2)
```

and put

```text
H=<D(F), e_(i_alpha,j_alpha)(r_alpha)> <= EL_n(R).
```

Then `H` is finite.

For `n>=5`, let `pi:St_n(R)->EL_n(R)` be the Steinberg projection,
let `F_tilde` be the lifted Thompson copy of `F), and choose the
standard root lifts `x_(i_alpha,j_alpha)(r_alpha)`.  Then

```text
Gamma=<F_tilde,x_(i_alpha,j_alpha)(r_alpha)>
```

fits into

```text
1 -> Z -> Gamma -> H' -> 1,                            (PSQ3)
```

where `H'<=H` is finite and `Z<=ker(pi)` is central.  Hence
`Gamma` is central-by-finite, amenable, and hyperlinear.

Consequently no finite family of mixed additive overlap projections supported
by the qutrit packet and finitely many positive Steinberg roots can complete a
no-CE algebraic atlas.  This conclusion is not a conjugacy, flat-Morita, or
same-code argument: it covers arbitrary coefficients in `C[H]` downstairs
and `C[Gamma]` upstairs.

In particular a single genuine Steinberg root does not escape the
finite-support basin, and the central `K_2` kernel does not rescue it.
The first surviving Steinberg bridge must leave the positive unipotent
radical, for example through an opposite-root commutator, Weyl/Whitehead
element, or a coefficient-return relation which mixes positive and negative
root directions.
