---
rg: 2
id: fp-group-rank-stability-equals-group-algebra-rank-stability
kind: claim
title: A finitely presented group is rank-stable over a field iff its group algebra is rank-stable
distinct_from:
  amenable-group-algebra-rank-stability-iff-rf: that is Bachner's weak pointwise stability criterion for amenable domains; this is the Bauer--Blachar--Greenfeld equivalence between flexible group rank-stability and flexible algebra rank-stability for every finitely presented group.
  atlas-rank-stability-literature-fence: that audits which published permanence theorems reach the augmented Atlas system; this imports the group--algebra equivalence and its two definitions as a claim other nodes can require.
artifacts:
  - research/artifacts/solve-weakly-sofic-2026-09-13.md
---

**ESTABLISHED (import).** Let `G = <x_1,...,x_d | P_1,...,P_r>` be finitely presented and `F` a field.
Then `G` is rank-stable over `F` iff `F[G]` is rank-stable.

**Definitions** (normalized rank `rk`, unnormalized rank `Rk`, `hat` pads a matrix with zeros):
- **Group** (Bauer--Blachar--Greenfeld Definition 6.1, after Elek--Grabowski). `G` is rank-stable over `F` if for every
  `eps > 0` there is `delta > 0` such that for every `n` and every `A_1,...,A_d` in `GL_n(F)` with
  `rk(P_j(A) - Id_n) < delta` for all `j`, there are `n'` and `B_1,...,B_d` in `GL_(n')(F)` with
  `P_j(B) = Id_(n')` for all `j` and `Rk(hat A_i - hat B_i) < eps n` for all `i`.
- **Algebra** (their Definition 1.1). The same, for a finitely presented algebra: approximate zeros of the relators,
  exact solutions of possibly different size `n'`.

The size `n'` may differ from `n`: the stability is flexible.

Citation route: `fp-group-algebra-rank-stability-citation`.
