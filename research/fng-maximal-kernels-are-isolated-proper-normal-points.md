---
rg: 2
id: fng-maximal-kernels-are-isolated-proper-normal-points
kind: claim
title: A maximal normal subgroup is finitely normally generated exactly when it is an isolated point of the Chabauty space of normal subgroups, so measure, genericity and limit constructions cannot certify one
distinct_from:
  fp-simple-groups-are-isolated: that places a finitely presented simple group among the isolated points of the space of MARKED GROUPS (Cornulier--Guyot--Pitsch, no novelty); items 1-3 here are the same phenomenon read inside the space of normal subgroups of one fixed group, and the new content is items 4-6 -- that every measure, entropy, Baire-generic or limit certificate misses these points, and that conjugation dynamics on normal subgroups is trivial.
  fp-quotient-iff-kernel-finitely-normally-generated: that equates finite presentability of a quotient with finite normal generation of its kernel, a purely algebraic statement; this equates finite normal generation of a MAXIMAL kernel with a TOPOLOGICAL property (isolation in the Chabauty space) and derives from it that no measure, Baire-category or limit argument can output such a kernel.
  kazhdan-hyperbolic-continuum-non-fng-maximal-kernels: that exhibits one Kazhdan hyperbolic group with continuum many non-finitely-normally-generated maximal kernels; this is a general dictionary valid for every finitely generated group, proves no existence or non-existence statement for any particular group, and explains the countable-versus-continuum phenomenon there as countability of the isolated points.
  ck-envelope-has-a-finitely-normally-generated-maximal-kernel: that is the open existence statement for the special CK envelope; this reformulates it (isolated maximal point) and kills one class of approaches to it, but does not prove or refute it.
  bi-index-core-makes-normals-core-class-unions: that describes the normal lattice through finite bi-index core classes; this is about the topology on the whole space of normal subgroups and uses no core or index hypothesis.
---

Let `Gamma` be a finitely generated group.  Let `N(Gamma)` be the set of
normal subgroups of `Gamma` with the Chabauty topology, which for discrete
`Gamma` is the product topology from `2^Gamma`.  Basic open sets are

```text
U(F, E) = { N in N(Gamma) : F subset N,  N cap E = empty },   F, E finite.
```

`N(Gamma)` is compact and metrizable.  Write `Max(Gamma)` for the set of
maximal proper normal subgroups and `Iso(Gamma)` for the set of isolated
points of `N(Gamma)`.

1. **(isolated implies fng)**  Every `N in Iso(Gamma)` is finitely normally
   generated.
2. **(dictionary)**  For `M in Max(Gamma)`: `M` is finitely normally
   generated if and only if `M in Iso(Gamma)`.
3. **(countability)**  The set of finitely normally generated normal
   subgroups is countable, so `Iso(Gamma)` is countable.  If `Gamma` is
   finitely presented, then `Gamma` has a finitely presented simple quotient
   if and only if `Max(Gamma) cap Iso(Gamma)` is nonempty.
4. **(measure obstruction)**  Let `mu` be any Borel probability measure on
   `N(Gamma)`.  Every finitely normally generated `M in Max(Gamma)` lying in
   `supp(mu)` is an atom of `mu`.  So the non-atomic part of `mu` gives mass
   zero to the finitely normally generated maximal kernels.  If a maximal
   kernel in `supp(mu)` has `mu({M}) = 0`, it is not finitely normally
   generated.
5. **(limit and genericity obstruction)**  Suppose `M in Max(Gamma)` is the
   Chabauty limit of normal subgroups `N_i != M`.  Then `M` is not finitely
   normally generated.  Consequently, a closed subset of `N(Gamma)` with no
   isolated points contains no finitely normally generated maximal kernel.
   Nor does any subset of `N(Gamma)` with no isolated points of its own:
   every point of such a set is a limit of other points of the set.
6. **(no dynamics on normal subgroups)**  Conjugation by `Gamma` acts
   trivially on `N(Gamma)`.  Hence every Borel probability measure on
   `N(Gamma)` is `Gamma`-invariant and `Gamma`-stationary for every step
   distribution.  The ergodic ones are exactly the Dirac masses.  In
   particular an ergodic invariant random subgroup supported on normal
   subgroups is a single normal subgroup.

Items 1 to 3 are the normal-subgroup reading of
[[fp-simple-groups-are-isolated]] and so are not new.  That node follows
Cornulier--Guyot--Pitsch, arXiv:math/0511714: a marked group is isolated
exactly when it is finitely presented and finitely discriminable.  Items 4
to 6 are the new content.  The route below does not import that result.  Its only
prerequisite is [[fp-quotient-iff-kernel-finitely-normally-generated]], and
only the finitely presented reading in item 3 uses it.

## Why it matters

The open hole [[ck-envelope-has-a-finitely-normally-generated-maximal-kernel]]
asks for a point of `Max(Gamma) cap Iso(Gamma)`.  Items 4 to 6 say that a
successful proof must name an **atom**, meaning a specific finite set `F`
with `<<F>>` maximal.  Positive measure, positive entropy, Baire
genericity, and convergence of a construction sequence can only certify
properties that hold off a countable set.  The target property is carried
by a countable set.
