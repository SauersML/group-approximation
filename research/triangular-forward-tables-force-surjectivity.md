---
rg: 2
id: triangular-forward-tables-force-surjectivity
kind: claim
title: A rule pair whose forward-sufficient partition eliminates triangularly is bijective over every group realizing it
distinct_from:
  certificate-controlled-routing-is-surjunctive: that proves surjectivity for certificate-controlled routing; this proves it for arbitrary nonlinear rules whose forward composite needs only coincidences that Tietze-eliminate one letter at a time.
  forward-memory-lifts-exclude-strict-cellular-sections: that needs a surjunctive cover to be supplied; this produces the cover, a free group, combinatorially from the partition.
artifacts:
  - research/artifacts/canonical-table-groups-for-automaton-designs-2026-09-12.md
  - research/artifacts/gk-vf-nonlinear-verification-2026-09-12.md
---

Let `D = (A, S, M, nu, mu)` be a design and `E` a forward-sufficient marked
partition of `S x M`, as in `strict-automata-live-on-canonical-table-groups`. Write
the relators of the table group `U_E` as freely reduced words in formal address
letters. Call `E` **triangular** if the relators can be ordered `r_1, ..., r_k` with
distinct letters `x_1, ..., x_k` such that `x_i` occurs exactly once in `r_i` and in
no later relator.

**Theorem.** If `E` is triangular, then over every group and every realization whose
forward table dominates `E`, the encoder `tau` is bijective and `tau sigma = id`.

The proof eliminates letters downward, so `U_E` is free. Free groups are residually
finite and surjunctive, so the realization over `U_E` is surjective. The table-group
homomorphism transfers the reverse identity to every realization.

**Consequences.**

- Every forward partition with at most one relator is triangular. With formal letters
  its four positions are distinct unless the relator collapses to `x_m = x_m'` or
  `x_s = x_s'`. A strict design needs at least two relators that cannot be eliminated.
- Collision-free composition rectangles have no relators, so they are covered.
- The decoder of a strict design must need a non-triangular core of coincidences, and
  by `strict-automata-live-on-canonical-table-groups` that core presents a nonsofic
  group.
