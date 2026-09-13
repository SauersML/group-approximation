---
rg: 2
id: vd-dehn-bounded-by-standard-square-word-area
kind: claim
title: The Dehn function of V_d is at most quadratic times the area of the standard square words at linear height
distinct_from:
  higman-thompson-vd-has-polynomial-dehn-function: that asserts a polynomial bound for V_d; this only reduces the Dehn function to one explicit family of null-homotopic words.
  thompson-v-has-quadratic-dehn-function: that asks for the sharp quadratic bound for V = V_2; this is a conditional polynomial reduction valid for every d.
artifacts:
  - research/artifacts/solve-vd-dehn-filling-2026-09-13.md
---

**Statement.** Fix `d >= 2`, a finite presentation `⟨S | R⟩` of `V_d`, and the
expansion cube complex `K_d` of `vd-expansion-cube-complex-is-cat0`.

**Canonical projection.** For a vertex `v = [φ]` of height `n`, order its pieces
by the lexicographically least point of each `φ(component)`, and let
`o_v : ⊔_n C_d -> ⊔_n C_d` be that reordering. Fix for each admissible `n` a
standard `d`-ary tree code `s_n : ⊔_n C_d -> C_d` with the leaves in
left-to-right order. Put

```text
r(v) = φ ∘ o_v ∘ s_n^(-1)  ∈  V_d .
```

This is well defined, since permuting the components is absorbed by `o_v`, and
`r` is the identity on height-one vertices.

**Standard words.**
- **Edges.** For an edge `v -> v'` that splits a piece, the element
  `r(v)^(-1) r(v') = s_n ∘ (o_v^(-1) σ o_(v')) ∘ s_(n+d-1)^(-1)` depends only on
  `n` and the combinatorial type of `o_v^(-1) σ o_(v')`: which standard
  component is split, and how its `d` pieces interleave with the rest. So there
  are finitely many such elements for each `n`. Fix a word `W(e)` in `S` for
  each.
- **Squares.** For a square with corner `v` of height `n`, splitting two distinct
  pieces, the square word `W(v->v_a) W(v_a->v_ab) W(v_b->v_ab)^(-1) W(v->v_b)^(-1)`
  is null-homotopic and ranges over a finite set `Q_n`. Put
  `A_d(n) = max { Area_R(q) : q ∈ Q_n }`.

**Conclusion.** There are constants `C, k_0` such that for all `L`

```text
δ_(V_d)(L) <= C·L + C·L^2 · max_{n <= k_0 + C·L} A_d(n).
```

So if `A_d` is polynomially bounded, so is `δ_(V_d)`.

**Status.** The route `vd-dehn-square-word-projection-proof` is complete modulo
the two OPEN imports `vd-expansion-cube-complex-is-cat0` and
`cat0-cube-loops-bound-quadratic-square-diagrams`.

**What this changes.** The recorded push-down argument (Attempts of
`higman-thompson-vd-has-polynomial-dehn-function`) pushes a filling down level
by level and multiplies costs. Projecting the whole CAT(0) filling at once
through `r` loses only a polynomial factor: the one remaining family is `Q_n`.
Square words are commutations of two disjoint splits at the standard tree,
conjugated by leaf permutations. So polynomial area of `Q_n` amounts to
polynomial area of the leaf-permutation Coxeter relators and the
split–permutation intertwining relators on standard trees. For `d = 2` that is
the π-word part of Lorrain's argument.
