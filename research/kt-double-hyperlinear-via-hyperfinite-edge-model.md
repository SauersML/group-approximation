---
rg: 2
id: kt-double-hyperlinear-via-hyperfinite-edge-model
kind: route
title: Model the Kazhdan subgroup by an amenable algebra so that Brown--Dykema--Jung adjoins the free lamp, then upgrade the abstract embedding
target: kt-double-mixed-word-trace-selection
requires: []
---

The attempt, recorded so that it is not retried.  By
`abstract-unitary-embedding-upgrades-to-hyperlinear`, hyperlinearity of the
free-lamp group `E = G *_Gamma (Gamma x C_2)` -- hence of the Kun--Thom double
`D = G *_Gamma G` (index two), hence `kt-double-mixed-word-trace-selection` --
follows from an abstract embedding `E -> U(N)` with `N` Connes embeddable.
Take an abstract model `pi : G -> U(R)` (one exists, `G` being residually
finite: tensor finite-dimensional representations padded with identities so
that the infinite tensor product converges), put `P = pi(Gamma)''`, which is
amenable because it sits in `R`, and form

```text
N = R *_P (P (x)-bar L(C_2)),
```

Connes embeddable by Brown--Dykema--Jung (arXiv:math/0609080, Corollary 4.5),
as the base `P` is hyperfinite -- exactly the hypothesis that fails for the
canonical base `L(Gamma)` in `hnn-hyperlinearity-is-amalgamated-free-haar-unitary`.
Send `G` to `pi(G)` and the lamp to the generator `s` of `L(C_2)`.  Britton
words `g_0 s g_1 s ... g_(m-1) s` with `g_i in G - Gamma` have, in the
amalgamated free product decomposition of `L^2(N)`, a top component
`pi(g_0)^o s pi(g_1)^o s ...` (`x^o = x - E_P(x)`), orthogonal to everything of
lower alternation length; the map is injective provided the relative tensor
products `pi(g_0)^o (x)_P ... (x)_P pi(g_(m-1))^o` never vanish, which holds
when `||E_P(pi(g))|| < 1` for all `g in G - Gamma`
(`exterior-hyperfinite-edge-model-amalgam-hyperlinear`).

**Dead.**  `amenable-kazhdan-models-absorb-compression`: because `Gamma` has
property (T) and `P` is amenable, `P` is atomic and every strict compressor
`t` of `Gamma` satisfies `pi(t^(-1) Gamma t) <= P`.  So for
`h in t^(-1) Gamma t - Gamma` one has `E_P(pi(h)) = pi(h)`, the top component
of the word `s h s h^(-1)` vanishes, and indeed `s pi(h) s pi(h)^(-1) = 1`
although `s h s h^(-1) != 1` in `E`.  No choice of `pi`, of the Connes
embeddable ambient, or of an amenable base `B >= P` (any such `B` contains
`pi(t^(-1) Gamma t)`) repairs this.  The only amalgamation permanence
available needs an amenable base, and for a compressed Kazhdan pair every
amenable base absorbs the compression.
