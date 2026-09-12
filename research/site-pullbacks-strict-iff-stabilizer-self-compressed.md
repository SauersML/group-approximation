---
rg: 2
id: site-pullbacks-strict-iff-stabilizer-self-compressed
kind: claim
title: A one-site equivariant self-map of a coset shift is strict exactly when a stabilizer is properly conjugated into itself
distinct_from:
  compressed-coset-shifts-carry-strict-equivariant-embeddings: that constructs a strict pullback when uHu^-1 < H; this classifies every one-site continuous equivariant self-map and shows strictness occurs only in that case, never on the full shift or a finite-stabilizer coset shift.
  full-shift-maps-to-infinite-stabilizer-coset-shifts-are-constant: that says the full shift maps only constantly into coset shifts with infinite stabilizers; this concerns self-maps of one coset shift that read a single site.
  end-fixing-tree-symmetries-carry-strict-automata: that is a strict automaton on a non-unimodular tree; this shows site-level strictness needs a stabilizer properly conjugated into itself, which for compact open stabilizers is exactly a failure of unimodularity.
artifacts:
  - research/artifacts/simple-host-direct-attack-2026-09-12.md
---

Let `G` be a group, `K <= G`, `X = G/K`, and `A` a finite alphabet with `|A| >= 2`.

- **Site maps:** the equivariant self-maps of `X` are `psi_c(gK) = gcK` with `c^-1 K c <= K`. All
  are onto, and `psi_c` is injective iff `c K c^-1 = K`.
- **One-site maps:** every nonconstant continuous equivariant `F: A^X -> A^X` whose value at each
  point reads a single site is `F(y) = theta o y o psi_c`, for some `theta: A -> A`.
- **Strictness:** `F` is injective iff `theta` is a bijection, and then `F` is strict iff `c^-1 K c`
  is a proper subgroup of `K`.
- **Finite stabilizers:** if `K` is finite, and in particular on the full shift, every injective
  one-site map is bijective.

So a Hilbert hotel on sites acts strictly exactly on a stabilizer properly conjugated into itself,
as in the compressed coset witness over `R^x`. It never acts strictly on the free regular action or
on the finite-stabilizer codomains of invariant-output designs. A strict automaton must read at
least two sites essentially.

Theorem 1 of the artifact.
