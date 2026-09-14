---
rg: 2
id: tower-simplicity-holds-for-topologically-free-actions
kind: claim
title: The elementary tower proof of simplicity needs only a minimal topologically free action, not a free one
distinct_from:
  finite-model-subshift-elementary-groups-simple-kazhdan-lef: that runs the tower proof for free minimal subshifts that have finite models, which forces a residually finite acting group; this weakens freeness to topological freeness and assumes nothing about models.
  steinberg-elementary-groups-are-simple-mod-centre: that is the groupoid criterion through local annihilation, stated for Steinberg algebras modulo the centre; this is the manuscript's own tower argument with one step replaced, and over `F_2` it gives simplicity on the nose.
  lamplighter-bernoulli-crossed-products-simple-kazhdan-lef: that is one family of hosts, and it takes simplicity from the Steinberg criterion; this is the general statement about the tower argument, and it makes that family self-contained.
  binary-el-simple-iff-minimal-topologically-free: that is the general mathematical statement, an equivalence over any countable acting group with the centre computed; this is the manuscript-facing form, which names the single sentence of the published proof that has to change and gives the replacement the note would print.
---

**ESTABLISHED (unreviewed).** Let `L` be a finitely generated group acting minimally and topologically freely on a
Cantor set `Z`, and let `R = LC(Z,F_2) ⋊ L` and `n ≥ 3`. Then `EL_n(R)` is an infinite simple group, finitely generated
when `R` is (for example when `Z` is a subshift over `L`), by the tower argument of `simple_kazhdan_sofic_group.tex` (main, rev1 5b1890ce6c) with one step replaced.

The manuscript's proof calls a clopen `V` *small* (for a fixed `g`, with `w` bounding the word length of the group
elements in the entries of `g` and `g^(-1)`) when `V ∩ ℓV = ∅` for every `ℓ ≠ 1` in the ball `B_(2w)`, and every
coefficient `f` of an entry of `g^(±1)` has `f ∘ α` constant on `V` for `α ∈ B_w`. It then uses

> every clopen set is a finite disjoint union of small ones,

which fails as soon as a point is fixed by some `ℓ ∈ B_(2w)`: a clopen set containing such a point has no small
partition, since `x ∈ V ∩ ℓV` for every neighborhood `V` of `x`. Replace it by

> every nonempty clopen set contains a small one,

which holds whenever the free points are dense, and dense free points follow from topological freeness by Baire. The
rest of the argument is unchanged: the tower units are `ε_(ab) = e_(aV) u_(ab^(-1))` for `a, b ∈ B_w`, the commutator
`[g, e_(ij)(e_V)]` lands in a copy of `GL_d(F_2)` with `d = n|B_w|`, and minimality covers `Z` by translates of `V`.

Only the step that produces a non-commuting `h = e_(ij)(e_V)` has to be rewritten, and the density version is shorter
than the manuscript's: see the route.

Consequences.
- The lamplighter hosts of `lamplighter-bernoulli-crossed-products-simple-kazhdan-lef` need no groupoid criterion; the
  manuscript's own proof covers them, so a note proving Theorem 1 proves the LEF embedding corollary with no new
  machinery.
- Freeness is used nowhere in the manuscript's simplicity proof. For a minimal `Z`-subshift the two hypotheses agree,
  since an infinite minimal subshift has no periodic points.

**Canonical form.** `binary-el-simple-iff-minimal-topologically-free` (sk-strong-4, landed concurrently) states the
mathematics in its strongest form: over `F_2` and for any countable acting group on a compact zero-dimensional space,
`EL_n` is simple exactly when the action is minimal and topologically free, with trivial centre. Cite that claim for
the mathematics. This node is kept for the manuscript: it identifies the one sentence of the published proof that
changes, l.143-144 of main `5b1890ce6c`, and its route gives the replacement text in the note's own notation. The two
repairs agree: small sets cover a dense open set, and a locally constant function vanishing on a dense set is zero.

Route: `tower-simplicity-topologically-free-proof`.

**Review (sk-verify-7, 2026-09-13, `research/artifacts/sk-review-7-2026-09-13-part1.md`):** PASS with scope repair R1: finite generation of `EL_n(R)` needs `R` finitely generated (the odometer is a counterexample), so the statement now says "finitely generated when `R` is"; the downstream lamplighter use is unaffected.
