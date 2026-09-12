---
rg: 2
id: finite-prototype-column-codes-force-coset-collisions
kind: claim
title: Finite-prototype column codes of unbounded chromatic number force unbounded normalized-row collisions
distinct_from:
  one-column-orbit-codes-have-bounded-chromatic-number: that treats one finite-order column orbit and assumes every normalized neighbour occupies a distinct cyclic coset; this permits finitely many mixed or opposite-root column prototypes and identifies unbounded fibre multiplicity as the only remaining escape.
  leavitt-chromatic-tables-have-area-divergence: that freezes a visibly persistent root column in two explicit Leavitt tables; this is a presentation-theoretic firewall for arbitrary graph blocks whose columns come from finitely many finite-order prototypes.
artifacts:
  - research/binary-leavitt-bounded-area-chromatic-code.md
---

**ESTABLISHED FINITE-PROTOTYPE COLLISION DICHOTOMY.**  Let
`Gamma=<S|R>` be finitely presented.  Fix nontrivial finite-order words
`beta_1,...,beta_r`.  Suppose finite graphs `G_n` have words
`c_v,h_v,b_v`, a type map `tau(v) in {1,...,r}`, and constants `A,B` such
that

```text
Area_R(h_v (b_v beta_(tau(v)) b_v^(-1))^(-1)) <= B,       (FPC1)
Area_R([c_w,h_v]) <= A                                    (FPC2)
```

for every oriented edge `v -> w`.  For a fixed column `v`, sort its outgoing
neighbours by the cyclic coset

```text
<beta_(tau(v))> b_v^(-1)c_wb_v
       in <beta_(tau(v))>\C_Gamma(beta_(tau(v))).          (FPC3)
```

If every fibre of `(FPC3)` has size at most one constant `K`, independent of
`n` and `v`, then the chromatic numbers of the underlying undirected graphs
are uniformly bounded.  Equivalently, a bounded-area code with unbounded
chromatic number and only finitely many finite-order column prototypes must
have fibres in `(FPC3)` of unbounded size.

Indeed, conjugating `(FPC2)` by `b_v^(-1)` and replacing the normalized
column by `beta_(tau(v))` costs at most `2B` cells.  Hence every normalized
neighbour is in the centralizer of its prototype and satisfies

```text
Area_R([b_v^(-1)c_wb_v,beta_(tau(v))]) <= A+2B.            (FPC4)
```

For each of the finitely many prototypes,
`finite-mark-centralizer-commutator-area-is-proper` makes the set of cyclic
cosets satisfying `(FPC4)` finite.  If `D` is the largest of those finite
cardinalities, every out-degree is at most `KD`.  Every induced subgraph
inherits the orientation, has average degree at most `2KD`, and is therefore
`(2KD+1)`-colourable.

This has a sharp consequence for proposed fixed-cell binary-Leavitt codes.
Suppose the columns are conjugates, through uniformly bounded comparison
cells, of finitely many root, Whitehead, mixed-root, or opposite-root torsion
words.  If after normalizing a column its neighbour rows lie in one fixed
elementary root subgroup and have distinct coefficients, then `(FPC3)` is
injective whenever that root subgroup meets the cyclic prototype trivially.
Thus `K=1`, and such a code cannot have unbounded chromatic number.  Replacing
the old root column by finitely many mixed/opposite-root fixed cells does not
evade the area obstruction while retaining separated root-row addresses.

The theorem does not rule out all chromatic compilers.  It identifies their
necessary new algebra: either infinitely many genuine column types, or
unboundedly many neighbours which become the same cyclic coset after the
column is normalized.  The cumulative, shift, Morita-tree, and ordinary
two-branch root tables have neither feature.

No Property `(T)`, Kazhdan input, matrix approximation, trace, or literature
theorem is used.

DERIVATION
finite-prototype-column-collision-proof
