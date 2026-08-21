---
rg: 2
id: fp-cayley-expanders-give-bounded-occurrence-edges
kind: claim
title: Finitely presented Cayley expanders give bounded occurrence edge words
distinct_from:
  regular-cayley-prototype-components-have-fixed-size: that classifies complete components of the full translated prototype graph; this uses selected finite expander subgraphs inside one infinite component.
  two-transitive-occurrence-sections-have-unbounded-pair-holonomy: that names cosets through global sections; this names every occurrence by an actual group element in a regular Cayley orbit.
  finite-orbit-occurrence-pauli-compiler: that still needs the full robust Pauli incidence rule and an exact marked model; this supplies only its expander-consistency geometry.
---

There is a finitely presented group `A`, a finite subset `D subset A`, and a
bounded-degree expander family `X_n` with injective vertex maps

```text
i_n:V(X_n)->A                                                     (FCE1)
```

such that every oriented expander edge `uv` satisfies

```text
i_n(u)^-1 i_n(v) in D.                                           (FCE2)
```

Consequently, for a root occurrence generator `a`, the word attached to a
vertex may be taken literally as

```text
A_(n,u)=i_n(u) a i_n(u)^-1.                                      (FCE3)
```

If `d=i_n(u)^-1 i_n(v)`, then an equality/consistency word on `uv` is the
conjugate by `i_n(u)` of the one prototype involving `a` and `d a d^-1`.
There are only finitely many `d`, so every expander consistency edge has
bounded relator cost independent of `n`, with no choice of a coset section
and no endpoint stabilizer holonomy.

The geometric input follows from the Sapir--Osajda embedding constructions:
Osajda constructs finitely generated graphical-small-cancellation groups
whose Cayley graphs contain expanders isometrically, and combines this with
Sapir's asphericity-preserving Higman embedding to obtain finitely presented
(indeed closed-aspherical-manifold) groups containing expanders
quasi-isometrically.  A uniform quasi-isometric upper bound on an expander
edge puts all relative differences in one finite word ball, giving `(FCE2)`.

This is a genuine positive result for the bounded-neighbor route: finite
presentability is compatible with literal bounded-scale expander occurrence
names.  It does **not** yet solve `finite-orbit-occurrence-pauli-compiler`.
The missing construction must place the whole degree-reduced Pauli
pair/linearity incidence system on such bounded-scale words, while ensuring
that all translated prototype relations have one exact infinite-dimensional
model with `J!=1`.  Imposing equality for every word in `D` globally may
collapse all occurrences in the subgroup `<D>`; separating the many logical
rows and columns remains load-bearing.

Literature inputs checked 2026-08-21:

- Damian Osajda, *Small cancellation labellings of some infinite graphs and
  applications*, Acta Math. 225 (2020), arXiv:1406.5015.
- Mark Sapir, *A Higman embedding preserving asphericity*, JAMS 27 (2014),
  arXiv:1103.3873.

