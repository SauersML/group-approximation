---
rg: 2
id: garden-of-eden-hinge-closure-folding-proof
kind: route
title: Quotient by a hinge closure makes the design surjective, and a periodic lift carries an unfolded orphan back
target: garden-of-eden-windows-fold-modulo-every-hinge-closure
requires:
  - strict-automata-live-on-canonical-table-groups
  - sofic-groups-are-surjunctive
artifacts:
  - research/artifacts/hinge-closure-window-folding-2026-09-12.md
---

Section 1 of the artifact.

By the canonical-table theorem, `sigma tau = id` over a group iff its forward table is
forward sufficient. When it is, `tau` is surjective iff its reverse table is reverse
sufficient. Both conditions are up-sets, and a quotient coarsens both tables.

Put `Q = H/N_P(H)`. The forward table of `Q` coarsens that of `H`, and the reverse table
of `Q` dominates `P` because every hinge word of `P` dies. So `tau_Q` is surjective. For
`z in A^Q` and the quotient map `q`, the identity `tau_H(z o q) = tau_Q(z) o q` holds
cell by cell. If `q` separated every pair of `Omega` with different symbols, some `z`
would restrict to `p` along `q`, its preimage `x_Q` under `tau_Q` would lift to
`x_Q o q`, and `tau_H(x_Q o q)` would show `p` on `Omega`. So `q` merges a
distinguished pair.

Conversely, if `tau` is surjective over `H/N`, its reverse table dominates a minimal
reverse-sufficient `P`, so `N ⊇ N_P(H)`. A homomorphism into a surjunctive group
realizes the design injectively, hence surjectively, so its kernel contains some
`N_P(H)`.

For two-cell windows the unique pair must fold for every `P`. The sofic radical is the
intersection of the kernels into sofic groups, and sofic groups are surjunctive, which
gives the containments.

For monolithic descent, Zorn's lemma gives `K` maximal among normal subgroups avoiding
`d`. The forward table over `H/K` coarsens, so the encoder stays injective. A copy of
`p` at `(K, dK)` in the image would lift to `(1, d)` in the image over `H`. Maximality
makes `dK` lie in every nontrivial normal subgroup.
