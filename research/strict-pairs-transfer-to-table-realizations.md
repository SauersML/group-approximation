---
rg: 2
id: strict-pairs-transfer-to-table-realizations
kind: claim
title: A strict automaton certificate transfers to every group realizing its product tables
distinct_from:
  forward-memory-lifts-exclude-strict-cellular-sections: that pulls a strict pair back along a surjunctive cover lifting the decoder rectangle injectively; this pushes a strict pair forward along any realization of the tables, allowing collisions except on cells the orphan pattern distinguishes.
  strict-automaton-tables-present-an-invisible-window-difference: that places a sofic-invisible element on a window difference of the table group; this shows every realization of the tables carries the same strict pair, so every homomorphism into any surjunctive group merges a distinguished window pair.
  sofic-radical-localizes-garden-of-eden-windows: that folds a window difference in almost-multiplicative permutation models of the memory group; this folds one under exact homomorphisms into arbitrary surjunctive groups, including nonsofic ones.
artifacts:
  - research/artifacts/gottschalk-table-realization-and-evasion-2026-09-12.md
---

**ESTABLISHED** by `strict-pair-table-realization-proof`.

**Setting.**
- `tau` and `sigma` are automata over a group `G`, with memories `M` and `S` that
  contain `1`, and `sigma tau = id`.
- `p in A^Omega` is a Garden of Eden for `tau`.
- `F = {1} ∪ M ∪ S ∪ Omega ∪ SM ∪ Omega M`.

**Theorem.** Suppose a group `K` admits a map `phi: F -> K` with

    phi(sm) = phi(s) phi(m),  phi(wm) = phi(w) phi(m)    (s in S, w in Omega, m in M),
    phi(w) != phi(w')         whenever p(w) != p(w').

Then the same local rules on `phi(M)` and `phi(S)`, with `p` moved to `phi(Omega)`,
form a strict pair over `K`. So `K` is not surjunctive. `phi` need not be injective
anywhere else.

**Corollaries.**
1. **Local embeddings.** If every finite subset of a group embeds, as a partial
   multiplication table, into some surjunctive group, then the group is
   surjunctive. Equivalently, surjunctive groups form a closed set in the space of
   marked groups.
2. **Quotient folding.** Put `H = <M ∪ S ∪ Omega>`. For every homomorphism `psi`
   from `H` into a surjunctive group, some `w, w'` in `Omega` with `p(w) != p(w')`
   have `psi(w) = psi(w')`. So every normal subgroup of `H` with surjunctive quotient
   contains such a difference `w^-1 w'`.
3. **Table groups.** The table group of
   `strict-automaton-tables-present-an-invisible-window-difference` is not
   surjunctive. Every homomorphism from it into a surjunctive group merges a
   distinguished window pair. For a coset-invariant output on `Omega = {1, h}`, every
   such homomorphism kills `x_h`.

**Use.** Corollary 3 is a filter that needs no local rules. Suppose a finite group,
or any group already proved surjunctive, realizes the products of candidate windows
with the distinguished cells kept apart. Then no local rules on those windows are
strict.

**Relation to earlier results.** Corollary 1 is the finite-table form of the
classical closure under marked limits. Lemma 3.1 of
`research/artifacts/lef-graph-wreath-surjunctivity-2026-09-12.md` is the case of an
injective `phi`. Section 3 of the linked artifact uses Corollary 1 as operation (O3)
of the permanence closure.
