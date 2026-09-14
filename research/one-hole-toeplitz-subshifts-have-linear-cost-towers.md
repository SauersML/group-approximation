---
rg: 2
id: one-hole-toeplitz-subshifts-have-linear-cost-towers
kind: claim
title: For a Toeplitz subshift with one hole per period p_k, the set {y_0 ≠ y_{p_k}} has no returns below p_k and transvections of length O(|A|p_k)
distinct_from:
  rotation-factor-subshifts-have-linear-cost-towers: that treats letters cut out by arcs of a rotation factor; this treats Toeplitz sequences with a single non-periodic residue class at each period.
---

**Hypothesis (T).**
- x ∈ A^Z is non-periodic.
- 1 = p_0 | p_1 | ⋯, and for each k ≥ 1 the positions not in Per_{p_k}(x) = {t : x_{t+jp_k} = x_t for all j} form a single residue class mod p_k.
- X is the orbit closure of x, and it is minimal.

Examples: period doubling and regular paperfolding (p_k = 2^k).

**Statement.** W_k = {y ∈ X : y_0 ≠ y_{p_k}} is nonempty and clopen, W_k ∩ T^tW_k = ∅ for 0 < |t| < p_k, and |e_ij(e_{W_k})| ≤ |A|(5 + 48p_k) in EL_3(LC(X,F_2)⋊Z).

**Status: established** by `one-hole-toeplitz-subshifts-have-linear-cost-towers-proof`. UNREVIEWED; queued with sk-referee-2.
