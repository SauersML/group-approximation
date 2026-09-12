---
rg: 2
id: full-shift-maps-to-infinite-stabilizer-coset-shifts-are-constant
kind: claim
title: Every continuous equivariant map from a full shift to the shift over a transitive set with infinite stabilizers is constant
distinct_from:
  subshift-self-embedding-carries-no-surjunctivity-content: that shows a strict self-embedding of a proper linear subshift carries no surjunctivity content; this shows the full shift cannot map nontrivially into coset shifts with infinite stabilizers at all, which closes the route of encoding configurations into Hilbert-hotel coset or boundary orbits.
---

Let `G` be a group, `A, B` finite alphabets, `X = G/K` a transitive left `G`-set
with `K` infinite, and `F: A^G -> B^X` continuous with
`F(g.x) = g.F(x)`, where `(g.y)(p) = y(g^-1 p)`. Then `F` is constant.

*Proof.* At the base point `o = K`, continuity gives a finite `D` in `G` and a
function `f` with `F(x)(o) = f(x|_D)`. For `h` in `K`, `h.o = o`, so equivariance
gives `F(h.x)(o) = F(x)(h^-1 o) = F(x)(o)`. Since `(h.x)|_D` is `x` read on
`h^-1 D`, the function `f` takes the same value on `x|_D` and on `x|_(h^-1 D)`.
The set `{h : h^-1 D meets D}` lies in `D D^-1`, which is finite, and `K` is
infinite. So some `h` in `K` has `h^-1 D` disjoint from `D`. Changing `x` on `D`
while holding `x|_(h^-1 D)` fixed leaves `f(x|_(h^-1 D))` unchanged, so `f` is
constant. The value `F(x)(o)` is thus independent of `x`. Transitivity and
equivariance give the same at every point. QED

**Consequence for Gottschalk constructions.** The G-set Hilbert hotels over the
Leavitt unit group live on infinite-stabilizer orbits:

- the coset action on `G/Gamma` for an infranormal Kazhdan subgroup, where
  `gGamma -> g u^-1 Gamma` is an equivariant surjection with infinite fibers;
- the boundary orbit of the Cantor set under Thompson's `V`.

No continuous equivariant encoding of the full shift into them exists, so a
strict automaton cannot be built by passing through such an orbit. Coset shifts
with finite stabilizers stay admissible; they are the invariant-output codomains
of `invariant-output-injective-automata-need-invisible-symmetry`.
