---
rg: 2
id: recurrent-orbit-closure-unique-minimal-set-proof
kind: route
title: Verification of the recurrent orbit closure with a unique Sturmian minimal set, and its normal subgroups
target: recurrent-orbit-closure-with-unique-sturmian-minimal-set
requires:
  - finitely-many-minimal-sets-el-normal-subgroups-are-kernels
artifacts:
  - research/artifacts/sk-k2-recurrent-2026-09-13.md
---

Details: `research/artifacts/sk-k2-recurrent-2026-09-13.md` §5.
1. **Recurrent.**
   - P ∩ [−N_k,N_k] is the set S_k of subsums of n_1..n_k, and P ∩ [n_{k+1}−N_k, n_{k+1}+N_k] = n_{k+1}+S_k. Both follow from the growth condition.
   - With the recurrence condition on y, x[−N_k,N_k] = x[n_{k+1}−N_k, n_{k+1}+N_k]. So T^{n_{k+1}}x → x.
2. **Not uniformly recurrent.** The times where the second coordinate is 1 are P, and the gaps n_{k+1} − N_k → ∞.
3. **Y = X_α × {0^∞}.** First coordinates lie in X_α. Long 1-free windows of x contain every Sturmian word, which recurs with bounded gaps in y.
4. **Bounded chains.** Given J, let k be least with n_{k+1}−N_k > J. Subsums differing above index k differ by more than J, so J-chains in P, and in every 1-set of a point of X, have at most 2^k elements.
5. **Unique minimal set.** A minimal set containing a 1 would have syndetic 1-sets, hence unbounded chains. So every minimal subset lies in Y ≅ X_α.
6. **Dictionary.** X has exactly one minimal subset, and it is infinite. `finitely-many-minimal-sets-el-normal-subgroups-are-kernels` gives the conclusion. □
