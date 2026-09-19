---
rg: 2
id: high-chromatic-sections-force-area-divergence
kind: claim
title: Hyperlinearity forces filling-area divergence in every high-chromatic conjugacy section
distinct_from:
  bounded-area-high-chromatic-conjugacy-collapse: that is the positive collapse criterion; this is its presentation-independent obstruction for every known hyperlinear group and explicitly identifies which area must diverge.
  literal-one-cell-carmichael-cliques-are-uniformly-finite: that rules out one literal fixed-template cell already in the ambient free group; this allows arbitrary diagrams and proves that their cell counts diverge in hyperlinear quotient groups.
  two-transitive-occurrence-sections-have-unbounded-pair-holonomy: that measures endpoint stabilizer corrections for two global sections; this applies to any high-chromatic conjugacy graph and any choice of word representatives.
---

Let `G=<X|R>` be finitely presented and hyperlinear, and let `w` be a word
which is nontrivial in `G`.  Suppose `Lambda_n` are finite graphs with
`chi(Lambda_n)->infinity`, and every vertex has a word

```text
u_v=h_v w h_v^(-1)
```

such that `u_v^3=1` and `(u_vu_z)^2=1` in `G` on every edge.  If

```text
sup_(n,v) Area_R(u_v^3)<infinity,                         (HAD1)
```

then

```text
max_(vz in E(Lambda_n)) Area_R((u_vu_z)^2) -> infinity.  (HAD2)
```

The conclusion is independent of the finite presentation and of the chosen
conjugating words.  In particular, a sofic or amenable finitely presented
group cannot provide the uniformly bounded-area high-chromatic section needed
by the matrix-collapse criterion around a nontrivial mark.
