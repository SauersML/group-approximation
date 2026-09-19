---
rg: 2
id: unbalanced-torus-forces-cross-gram-on-ambient-face
kind: claim
title: On the ambient-exact face one unbalanced word forces the first HNN cross-Gram to modulus one
distinct_from:
  unbalanced-torus-blocks-spectator-free-lamp-models: that treats one pure tensor denominator coordinate and proves the elementary sharp bound 1-2 eta; this permits arbitrary direct sums, cross-block mixing and unbounded operator-Schmidt rank, with additional overlap and lattice-centrality errors.
  unbalanced-torus-extracts-near-central-denominator-coordinate: that proves projective transfer for every auxiliary unitary near an exact ambient reference; this specializes to the HNN letter, identifies the target projective commutator with the first quasiregular cross-Gram, and states the resulting obstruction to all blockwise spectator models.
  sl3-amalgamated-free-enemies-are-ambient-extension-outliers: that concludes every full amalgamated-free enemy is uniformly far from exact ambient restrictions; this gives the quantitative one-cross-Gram inequality which proves that localization.
---

Put

```text
C=SL_3(Z),       A=SL_3(Z[1/p]),
h=diag(p,1,p^(-1)),       C_+=C intersect hCh^(-1).
```

Fix the generating sets `S` and `S_+` and constants `K,C_0` of
`unbalanced-torus-extracts-near-central-denominator-coordinate`.  Let
`sigma:A->U(d)` be an arbitrary exact finite-dimensional representation,
and let `H,T in U(d)`.  Define

```text
q_C(T)=sum_(s in S)(1-|tr([T,sigma(s)])|^2),
eta=||ev_(sigma|C,H)(R_tor)-I||_2,

alpha_+(H)=sum_(c in S_+)
 ||H sigma(h^(-1)c h) H^*-sigma(c)||_2^2.               (ACG1)
```

Then

```text
1-|tr(T^*H^*TH)|^2
 <=K q_C(T)+C_0 eta^2+C_0 alpha_+(H).                   (ACG2)
```

In particular, if `T` centralizes the exact lattice actor, `H` implements
the fixed overlap conjugacies, and the unbalanced torus word is exact, then

```text
|tr(T^*H^*TH)|=1.                                      (ACG3)
```

The amalgamated-free HNN value is zero, so `(ACG3)` excludes it.

No multiplicity hypothesis occurs.  The exact ambient representation may
be any finite direct sum with arbitrary multiplicities, and `H,T` may mix
all its blocks.  Thus `(ACG2)` covers every bounded operator-Schmidt-rank
spectator model, and indeed models of unbounded Schmidt rank, as long as the
three displayed ambient-face errors are small.  One fixed cross-Gram is
already sufficient; taking more free-lamp moments cannot enlarge this
closed sector.

The scope is the exact boundary.  If the lattice tuple is not close to the
restriction of any exact same-dimensional representation of `A`, there is
no `sigma` to which `(ACG2)` can be applied.  That is precisely the
ambient-extension outlier isolated in
`sl3-amalgamated-free-enemies-are-ambient-extension-outliers`; bounded
Schmidt rank by itself does not manufacture the missing ambient reference.
