---
rg: 2
id: relative-coset-pauli-incidence-compiler
kind: claim
title: A separated typed Cayley incidence family compiles to one marked group
distinct_from:
  fp-cayley-expanders-give-bounded-occurrence-edges: that supplies bounded-word expander edges but no row/column or sign separation; this proves the group theorem once that stronger typed placement is given.
  occurrence-local-dimension-games-force-mark-collapse: that is the abstract terminal dimension argument; this supplies a concrete finite presentation and proves exact nontriviality of its central mark.
  two-transitive-occurrence-sections-have-unbounded-pair-holonomy: that compares section-named endpoints; this uses actual Cayley addresses and encodes endpoint gauge freedom as cosets.
---

Let `A` be finitely presented.  Fix finite subsets

```text
D_X,D_Z,P_0,P_1 subset A,      H_X=<D_X>, H_Z=<D_Z>.             (RCI1)
```

Assume the sign double cosets are disjoint:

```text
H_X P_0 H_Z  intersect  H_X P_1 H_Z = empty.                    (RCI2)
```

Suppose there are finite typed incidence graphs `C_N` with X-occurrence
vertices addressed by elements `g_v in A` and Z-occurrence vertices addressed
by `h_w in A`, satisfying:

1. an X-equality edge has `g_u^-1 g_v in D_X`, and its connected components
   inject into `A/H_X`;
2. a Z-equality edge has `h_u^-1 h_v in D_Z`, and its connected components
   inject into `A/H_Z`;
3. a sign-`b` pair edge has `g_v^-1 h_w in P_b`;
4. the reflection games represented by these equality and pair edges have
   perfect completeness and a fixed robust dimension bound `D_N->infinity`.
   Finitely many bounded local product/linearity decorations are allowed as
   well, provided their address templates hold in the exact coset-Clifford
   model below and are imposed by finitely many further prototype relators.

Then the finite presentation obtained from `A` by adjoining involutions
`x,z,J`, making `J` central, and imposing

```text
[x,d]=1                 (d in D_X),
[z,d]=1                 (d in D_Z),
[x,p z p^-1]=J^b        (p in P_b, b=0,1)                       (RCI3)
```

has `J!=1` in an exact infinite-dimensional representation.  Moreover every
sufficiently accurate finite-dimensional tuple in which the marked `J`
sector survives decodes, with constants independent of `N`, to a strategy
for every `C_N` on the same matrix space (up to one fixed local extraction).
Consequently the marked sector collapses in finite microstates, and the
group is nonhyperlinear whenever the standard central-mark extraction has
threshold below `sqrt(2)`.

The significant point is exact completeness.  Condition `(RCI2)` lets one
write an explicit `A`-invariant infinite bipartite Clifford form on the two
coset spaces.  No appeal to a hoped-for compatibility of the finite games is
needed.

For nondegenerate Pauli sign tables, the two cloud-injectivity assumptions
can be replaced by row/column separation of the tested sign profile:
`sign-double-cosets-separate-pauli-clouds` derives injectivity directly from
`(RCI2)`.

The last sentence in clause 4 is load-bearing for an application to a Pauli
braiding/linearity game: the equality and signed-pair presentation is the
unbounded incidence core, while the finite local decorations must still be
checked in the exact Clifford model.  The theorem does not silently discard
those tests.
