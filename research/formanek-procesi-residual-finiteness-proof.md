---
rg: 2
id: formanek-procesi-residual-finiteness-proof
kind: route
title: Embed the diagonal HNN in an automorphism group and use characteristic finite quotients
target: formanek-procesi-diagonal-hnn-is-residually-finite
requires: []
---

Bardakov--Mikhailov define `(FPH1)` and construct an injective homomorphism

```text
H(L) -> Aut(L * <z>).                                    (FPH2)
```

The two copies of `L` act by inner automorphisms and by right transvections
of `z`, while the stable letter acts by conjugation by `z`.  Their normal-form
argument proves injectivity because the center of the nontrivial free product
`L*Z` is trivial.

For completeness, if a group `G` is finitely generated and residually finite,
then `Aut(G)` is residually finite.  Given a nonidentity automorphism `alpha`,
choose `g` with `alpha(g)!=g` and a finite-index normal subgroup `N` avoiding
`alpha(g)g^(-1)`.  A finitely generated group has only finitely many subgroups
of any bounded index.  Intersecting all subgroups of index at most `[G:N]`
gives a finite-index characteristic subgroup `C<=N`.  The automorphism induced
by `alpha` on the finite group `G/C` is nonidentity, so finite automorphism
quotients separate `Aut(G)`.

Free products of residually finite groups are residually finite, so
`G=L*Z` satisfies the hypothesis.  Equation `(FPH2)` then makes `H(L)`
residually finite.  Finally, replacing `s` by `t^(-1)` converts `(FPH1)` into
`(DHA2)` term by term.
