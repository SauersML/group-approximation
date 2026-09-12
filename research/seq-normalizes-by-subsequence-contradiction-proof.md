---
rg: 2
id: seq-normalizes-by-subsequence-contradiction-proof
kind: route
title: Extract a bounded-below subsequence, reindex the sofic approximation along it, and apply the finite obligation there
target: seq-normalizes-by-subsequence-contradiction
requires: []
artifacts:
  - GroupApproximation/KunThom/SequentialContradiction.lean
---

Proved in Lean in `GroupApproximation/KunThom/SequentialContradiction.lean`, landed at
f3ea74313 with its root import.

- **Probe.** GREEN record `kt41-seq-wrapper.green.0912-130804-24253` (base b1381e41a,
  md5 ce04ad1b68c42172d66b12d7740ab671).
- **Axioms.** All ten printed closures are `[propext, Classical.choice, Quot.sound]`,
  including the three `seqNormalizes_of_*` theorems and both diagonal lemmas.

1. **Extraction.** `Nat.exists_strictMono_subsequence` gives
   `exists_strictMono_of_frequently`. Then `exists_strictMono_le_abs_of_not_vanishing`
   turns a nonvanishing sequence into `eps > 0` and a strictly increasing `phi` with
   `eps <= |a (phi k)|`.
2. **Reindexing.** A strictly increasing `phi` dominates the identity
   (`le_apply_of_strictMono`). `SoficApproximation.reindex A phi` is a sofic
   approximation, and `almostCommutes_reindex` is `Vanishing.reindex`.
3. **Obligation 1.** Given a nonvanishing defect, apply the hypothesis to
   `A.reindex phi` and `v o phi`. The reindexed defect at `k` is definitionally the
   original defect at `phi k`, which is at least `eps`.
4. **Obligation 2.** A subsequence along which the defect vanishes has a term below
   `eps`, which contradicts the bound of obligation 1.
5. **Obligation 3.** Direct, with no contradiction.
   - `almostCommutes_eventually_finset` makes `v_n` `delta`-commute with `A_n(F)`
     eventually.
   - The hypothesis at `w = v_n` then bounds the conjugated defect below `eps`.
   - `vanishing_of_eventually_lt` concludes.
6. **Slow diagonal.** Choose thresholds `M i` for each eventual property. Put
   `j n = Nat.findGreatest (fun k => forall i < k, M i <= n) (f n)`.
   - `j n <= f n` holds by construction.
   - `j n >= K` once `n >= f`'s threshold for `K` and `n >= sum_{i<K} M i`.
   - For the vanishing version, apply it to the properties
     `forall i' <= i, |a i' n| < 1/(i+1)`.
