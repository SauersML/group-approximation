---
rg: 2
id: rotation-factor-subshifts-have-linear-cost-towers
kind: claim
title: If a letter of a minimal subshift is sandwiched by an arc of an irrational rotation factor, the sets {x_0 = a, x_{q_n} ≠ a} have no returns below q_{n+1} and cost O(q_n)
distinct_from:
  sturmian-elementary-group-lef-growth-is-exp-r-squared: that uses two positive letter conditions tied to the Sturmian arc endpoints; this uses the letter-change set [a] minus T^{-q}[a] for any letter sandwiched by an arc of any rotation factor.
---

**Hypothesis (R).**
- π: X → R/Z is a continuous surjection with π(Tx) = π(x) + α, where α is irrational.
- a is a letter and I = [β, β') is an arc with 0 < |I| < 1 such that `π^{-1}(int I) ⊆ [a] ⊆ π^{-1}(cl I)`.

This covers Sturmian subshifts and every coding of an irrational rotation by finitely many intervals, for every letter.

**Statement.** Let p_n/q_n be the convergents of α and η_n = q_nα − p_n. Suppose |η_n| < min(|I|, 1 − |I|), and put q = q_n. Then:
- `W = {x : x_0 = a, x_q ≠ a}` is a nonempty clopen set;
- W ∩ T^tW = ∅ for 0 < |t| < q_{n+1};
- |e_ij(e_W)| ≤ 5 + 48q in G_X = EL_3(LC(X,F_2)⋊Z), with the generators {e_ij(s) : s ∈ {1, u^{±1}, e_a}}.

**Idea.**
- π(W) lies in a closed arc of length |η_n| at one end of I. So a return t forces ‖tα‖ ≤ |η_n|, hence t = ±q_n by best approximation.
- The two letter conditions themselves exclude t = ±q_n.
- Cost: e_W = e_a + e_a u^{-q} e_a u^q, a single commutator.

**Status: established** by `rotation-factor-subshifts-have-linear-cost-towers-proof`. UNREVIEWED; queued with sk-referee-2.

**Review (sk-verify-7, 2026-09-13, `research/artifacts/sk-review-7-2026-09-13-part3.md`):** PASS; every step re-derived (see the artifact).
