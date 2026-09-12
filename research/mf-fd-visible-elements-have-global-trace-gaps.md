---
rg: 2
id: mf-fd-visible-elements-have-global-trace-gaps
kind: claim
title: Finite-dimensional visibility gives a global trace gap in every MF group
distinct_from:
  mf-invariant-corner-visibility: That open claim treats every nontrivial element of an MF group, including elements in the finite-dimensional residual; this theorem treats exactly the complementary elementwise regime and obtains the stronger choice P=1.
  mf-finite-normal-tracially-visible: That theorem extracts an isotypic corner from an arbitrary MF realization when the element lies in a finite normal subgroup; this theorem changes the realization by adjoining one exact finite-dimensional representation and needs no finite or normal subgroup.
  regular-character-mf-trace-implies-group-mf: That theorem starts from operator-norm microstates for the whole regular character and concludes weak MF; this theorem starts from weak MF plus one exact finite-dimensional separator and manufactures only the prescribed elementwise trace gap.
---

Let `G` be a countable MF group and let `g in G`.  If some
finite-dimensional unitary representation

```text
rho : G -> U(m)
```

satisfies `rho(g) != I_m`, then there is a faithful matrix-corona
homomorphism `v : G -> U(Q)` such that

```text
limsup_n Re tr(v_n(g)) < 1.                              (FDV1)
```

In particular the conclusion of `mf-invariant-corner-visibility` holds for
`g` with the global invariant projection `P=1`.

Equivalently, any counterexample pair `(G,g)` to invariant-corner
visibility must satisfy

```text
1 != g in Rad_fd(G) \ Rad_MF(G).                         (FDV2)
```

For an MF group `Rad_MF(G)=1`, so `(FDV2)` says that the first genuinely
unresolved regime is not merely non-LEF or non-residually-finite: the marked
element must be invisible in every exact finite-dimensional unitary
representation while remaining visible to operator-norm almost
representations.
