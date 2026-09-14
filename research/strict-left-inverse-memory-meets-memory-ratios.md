---
rg: 2
id: strict-left-inverse-memory-meets-memory-ratios
kind: claim
title: The left inverse of a strict automaton has a nontrivial memory element in M M^-1
distinct_from:
  forward-memory-lifts-exclude-strict-cellular-sections: that says a strict cellular section must use some forward equality s m = s' m' that a surjunctive cover separates; this names which equality, one with m' = 1 in the identity row, and needs no cover.
  forward-relations-of-a-counterexample-have-a-nonsofic-core: that peels the forward relator hypergraph to a nonsofic two-core; this is a pointwise condition on the decoder memory, which the core theorem does not give, since square relators alone can form a core.
  surjunctivity-is-axiomatized-by-rectangle-clauses: that characterizes nonsurjunctive groups by realized strict rectangle data; this adds that every realized strict forward table joins the identity row to another row.
---

**ESTABLISHED** by `strict-left-inverse-memory-meets-memory-ratios-proof`.

Let `G` be a group, `A` a finite alphabet, and `tau: A^G -> A^G` a cellular automaton
with memory `M` (containing `1`) and local rule `mu`. Let `sigma` be a cellular automaton
with memory `S` (containing `1`) and rule `nu` such that `sigma tau = id`.

**Theorem.** If `tau` is not surjective, then some `s` in `S`, `s != 1`, lies in `M M^-1`.
Equivalently, `s m' = m` for some `m, m'` in `M`.

In the language of rectangle data: every strict data set realized in a group has a forward
coincidence joining a cell `(1, m)` of the identity row to a cell `(s, m')` with `s != 1`.
This strengthens Proposition 3 of `research/artifacts/boolean-core-alphabets-and-network-coding-2026-09-12.md`
(a discrete forward table forces the reverse identity): only the identity row has to be
separated from the other rows.

**Filter.** A pair of memories `(M, S)` with `S ∩ M M^-1 = {1}` in the ambient group carries
no strict pair for any alphabet and any rules. For example the decoder memory `S` of a strict
pair can never be chosen inside a subgroup meeting `M M^-1` only in `1`.
