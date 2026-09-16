---
rg: 2
id: effaceable-cohomology-makes-inflation-an-isomorphism
kind: claim
title: If every finite-coefficient class of degree 1 to n dies on a finite-index subgroup, inflation from the profinite completion is an isomorphism through degree n
distinct_from:
  good-groups-have-no-persistent-finite-cohomology: that is the converse direction, goodness forces every positive-degree finite-coefficient class to die on a finite-index subgroup; this derives inflation isomorphisms from that vanishing, degree by degree, and is what turns effacement results into goodness
  degree-two-inflation-onto-makes-z-extension-centres-survive: that consumes surjectivity of degree-two inflation with trivial cyclic coefficients to make centres of central Z-extensions survive; this produces bijectivity of inflation in all degrees up to n from effaceability, with no extension-theoretic consequence
artifacts:
  - research/artifacts/hyperbolic-goodness-rf-plus-high-degree-reduction-2026-09-16.md
---

Let `G` be any group and `n >= 0`. A class `x in H^q(G;M)` is *effaceable* if
`res^G_W(x) = 0` for some finite-index subgroup `W <= G`. Assume

```text
(E_n)  for every finite G-module M and every 1 <= q <= n,
       every class in H^q(G;M) is effaceable.
```

Then

```text
(A_n)  for every finite G-module M and every 0 <= q <= n,
       inf: H^q(G_hat;M) -> H^q(G;M) is an isomorphism.
```

In particular, if every positive-degree finite-coefficient class on `G` is
effaceable, then `G` is good in Serre's sense.

Here a finite `G`-module is a finite abelian group with a `G`-action whose kernel
has finite index, and `H^q(G_hat;M)` is continuous cohomology. With
[[good-groups-have-no-persistent-finite-cohomology]], this makes goodness of `G`
equivalent to effaceability of all positive-degree finite-coefficient classes.

This is the classical criterion posed as an exercise in Serre, *Galois
Cohomology*, Ch. I, §2.6, Exercises 1-2 (recalled, not fetched). No novelty is
claimed. The route [[effaceable-cohomology-makes-inflation-an-isomorphism-proof]]
gives a self-contained proof by induction on `n` using the coinduced module
`Map(G/U,M)`, so the graph does not depend on the unfetched exercise.
