---
rg: 2
id: seq-normalizes-by-subsequence-contradiction
kind: claim
title: Sequential per-compressor normalization reduces to refuting a uniform lower bound in every sofic approximation
distinct_from:
  kun-thom-sofic-centralizer-normalization: that is Kun--Thom Theorem 4.1 itself; this is only the sequential-to-finite glue, which turns a finite argument about one approximation into SeqNormalizes and proves nothing about centralizers.
  lef-criteria-miss-sequential-kun-thom-normalization: that records why the LEF criteria and exact collapses do not prove the per-compressor core; this is the landed reduction of that core to finite obligations.
artifacts:
  - GroupApproximation/KunThom/SequentialContradiction.lean
---

Let `Gamma <= G` be groups and `g in G`. Recall that `SeqNormalizes Gamma g` asks, for every
sofic approximation `A` of `G` and every sequence `v` almost commuting with `A(Gamma)`,
that `A(g) v A(g)^-1` almost commutes with `A(Gamma)` along `Filter.atTop`.

Each of the following three obligations implies `SeqNormalizes Gamma g`:

1. **Uniform lower bound refuted** (`seqNormalizes_of_forall_not_uniform_lower_bound`).
   No `A`, `v`, `gamma in Gamma` and `eps > 0` have
   `eps <= d_H(A(g) v_n A(g)^-1 A_n(gamma), A_n(gamma) A(g) v_n A(g)^-1)` at every index `n`.
2. **Vanishing along a subsequence** (`seqNormalizes_of_exists_strictMono_vanishing`).
   For every `A`, `v`, `gamma`, that defect vanishes along some strictly increasing
   subsequence.
3. **Uniform finite estimates** (`seqNormalizes_of_eventually_uniform`).
   For every `A`, `gamma in Gamma` and `eps > 0` there are:
   - a tolerance `delta > 0`;
   - a finite `F` contained in `Gamma`;
   - a threshold `N`.

   Then every permutation `w` of the `n`-th model, `n >= N`, that `delta`-commutes with
   `A_n(F)` has `A_n(g) w A_n(g)^-1` `eps`-commuting with `A_n(gamma)`.

The mechanism for 1 and 2:
- a nonvanishing defect stays at least some `eps` above zero along a strictly increasing
  `phi`;
- `SoficApproximation.reindex` along `phi` is again a sofic approximation, so freeness and
  multiplicativity survive by construction;
- almost commutation transfers by `SoficApproximation.almostCommutes_reindex`.

The same module provides the diagonal lemmas the finite argument needs:
- uniform smallness of finitely many vanishing sequences;
- a slow `j n -> infinity`, below any prescribed `f n -> infinity`, with the first `j n`
  eventual properties holding at index `n` (`exists_diagonal_of_eventually`,
  `exists_diagonal_vanishing`);
- one witness per bad index along a subsequence (`exists_strictMono_choice`).

Scope:
- This claim establishes nothing about the per-compressor core. The core still needs a
  finite argument meeting one of the three obligations.
- An argument written exactly in the ultraproduct over one nonprincipal ultrafilter meets
  obligation 1 only if it applies to every sofic approximation, reindexed ones included,
  because obligation 1 quantifies over all of them.
- Only the direction from obligation 3 to `SeqNormalizes` is formalized. The converse, for
  countable `Gamma`, is not needed by the endpoint.

Derivation: `seq-normalizes-by-subsequence-contradiction-proof`.
