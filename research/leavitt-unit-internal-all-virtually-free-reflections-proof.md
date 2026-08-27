---
rg: 2
id: leavitt-unit-internal-all-virtually-free-reflections-proof
kind: route
title: Turn a demonstration node in Thompson's group into a regular family of Leavitt corners
target: leavitt-unit-internal-all-virtually-free-reflections
requires:
  - wandering-leavitt-corner-reflection-compiler
  - leavitt-cylinder-swaps-generate-thompson-in-el
---

Bennett and Bleak prove that every countable virtually free group has a
demonstrative embedding in Thompson's group `V`, and that a finitely generated
group has such an embedding exactly when it is virtually free
(`A dynamical definition of f.g. virtually free groups`, Theorem 1 and
Section 2.1, arXiv:1510.02638).

For a demonstrative embedding there is a binary word `v` such that the
cylinder

```text
D=[v]
```

satisfies

```text
D intersect qD=empty                              (1!=q in Q).   (AVFP1)
```

Applying `(AVFP1)` to `q^(-1)q'` gives

```text
qD intersect q'D=empty                            (q!=q').      (AVFP2)
```

The standard prefix-table realization of `V` lies in `U`.  Let

```text
s=s_v,                  t=t_v,                  p=st.
```

The Leavitt prefix relations give `ts=1`, and `(AVFP2)` says precisely that
the idempotents `q p q^(-1)` are pairwise orthogonal.  The wandering-corner
reflection compiler now supplies the internal embedding `(AVF2)`, the
radical and reflection formulas `(AVF3)`, the Hom bijection `(AVF4)`, and the
semantic formulas `(AVF5)` and `(AVF6)`.

A countable virtually free group is residually finite.  Indeed, pass to a
free finite-index subgroup, take its finite-index normal core, and separate
an element inside that core by a finite quotient of the free group; the
finite intersection of its conjugates is normal in the whole group.  Thus
`Q` is MF, so `(AVF3)` has exactly the displayed base kernel.  A fixed
nonidentity involution normally generates `U`, and its `Q`-conjugates reach
every coordinate, proving single normal generation.  Triviality of all maps
from `U` to each of the other stated target classes proves their Hom
factorizations in the same way.

If `Q` is finitely generated, one finite generating set for `U` in the
identity corner together with generators of `Q` generates `W_Q`.  The
nonisomorphism assertion follows by applying universal MF reflection.

Finally, a wandering prefix-table corner is the cylinder form of a
demonstration node.  Bennett--Bleak's forward construction proves existence
for virtually free groups, and their converse says that every finitely
generated demonstrable subgroup of `V` is virtually free.  This proves the
first three conditions and the maximality statement.  The theorem of
Muller--Schupp identifies finitely generated groups with context-free word
problem exactly with the virtually free groups, adding the fourth equivalent
condition.
