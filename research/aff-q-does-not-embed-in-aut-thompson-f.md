---
rg: 2
id: aff-q-does-not-embed-in-aut-thompson-f
kind: claim
title: Aff(Q), SL_2(Q) and GL_2(Q) embed neither in T-bar nor in Aut(F), and T-bar contains no Q^2
distinct_from:
  gl-n-q-embeds-in-fp-simple-group: that is the open embedding question for GL_n(Q) into some finitely presented simple group; this excludes two specific finitely presented hosts, T-bar and Aut(F), for n = 2 and for the affine and unipotent stepping stones.
artifacts:
  - research/artifacts/gq-gq-lit-q-embeddings.md
---

**ESTABLISHED** through `aff-q-does-not-embed-in-aut-thompson-f-proof`. This is a lane
proof from verbatim-cited statements of Belk–Hyde–Matucci and Brin, not independently
reviewed. No priority is claimed; the novelty search was bounded to the sources in the
artifact.

**Notation.**
- `T̄` is the group of Belk–Hyde–Matucci (arXiv:2005.02036v4): homeomorphisms of `R`
  that are piecewise linear with finitely many breakpoints on each compact interval,
  with pieces `x ↦ 2^n x + d` (`n ∈ Z`, `d` dyadic) and dyadic breakpoints, commuting
  with `z(x) = x + 1`. Its centre is `⟨z⟩`.
- `F` is Thompson's group. `Aut(F)` has index-two subgroup `Aut₊(F)` (Brin's `A`).

**Statement.**
1. `T̄` contains no subgroup isomorphic to `Q × Q`. Hence `T̄` contains no copy of `Q^n`
   for `n ≥ 2`, and none of `U_3(Q)`.
2. Let `N ≤ T̄` with `N ≅ (Q,+)`. No element of `T̄` normalizes `N` and acts on it by a
   nontrivial automorphism. (Every automorphism of `(Q,+)` is multiplication by some
   `λ ∈ Q^x`.)
3. Let `H` be a group with a subgroup `N ≅ (Q,+)` and a subgroup `L ≤ N_H(N)` with the
   following property. For every subgroup `L'` of index at most 2 in `L`:
   - some element of `L'` acts on `N` nontrivially, and
   - the only `L'`-invariant subgroups of `N` are `1` and `N`.

   Then `H` does not embed in `Aut(F)`.
4. Consequently none of `Aff(Q) = Q ⋊ Q^x`, `SL_2(Q)`, `GL_2(Q)` embeds in `Aut(F)`, and
   none of them embeds in `T̄`. Neither does any group containing one of them, such as
   `SL_n(Q)`, `GL_n(Q)`, `B_n(Q)` for `n ≥ 2`.

**Scope.** `T̄ ≤ Aut₊(F) ≤ VA`. The statement says nothing about `VA`, where disjoint
supports give `⊕_ω Q` and the germs are not confined to `±∞`. For `n ≥ 3`, VA is
already excluded by `SL_3(Z)` (survey Remark 4.12). **For `n = 2`, VA stays open.**
