---
rg: 2
id: radu-lattice-is-limit-of-nilpotent-by-arithmetic-groups
kind: claim
title: Radu's BMW lattice is a marked limit of free-nilpotent-by-arithmetic groups, so its soficity is an instance of amenable-by-sofic permanence
distinct_from:
  radu-horizontal-quotient-is-arithmetic-lattice: that identifies the quotient by the free kernel as an arithmetic lattice; this uses the lower central series of that kernel to approximate the lattice by amenable-by-arithmetic groups
  sofic-kernel-amenable-quotient-permanence: that is the established direction, sofic kernel with amenable quotient; this reduces Radu's lattice to the open direction, amenable kernel with sofic quotient
---

**ESTABLISHED (unreviewed).** Let `Λ_v <= Γ_R` be the free kernel and `Q = Γ_R/Λ_v` the cocompact
arithmetic lattice in `PGL_2(Q_2) × PGL_2(Q_2)` of `radu-horizontal-quotient-is-arithmetic-lattice`.
Let `γ_k(Λ_v)` be the lower central series of `Λ_v`, and put

```text
G_k = Γ_R / γ_k(Λ_v),        1 → Λ_v/γ_k(Λ_v) → G_k → Q → 1.
```

1. **Approximation.** Each `γ_k(Λ_v)` is characteristic in `Λ_v`, hence normal in `Γ_R`, and
   `∩_k γ_k(Λ_v) = 1` because free groups are residually nilpotent. So `G_k → Γ_R` in the space
   of marked groups. Each `G_k` is an extension of an infinitely generated free nilpotent group
   of class `k − 1` by the residually finite linear group `Q`.
2. **Positive horn.** If every `G_k` is sofic, then `Γ_R` is sofic, because soficity is closed
   under marked limits.
3. **Negative horn.** If `Γ_R` is not sofic, some `G_k` is a nonsofic extension of an amenable
   group by a residually finite linear group. That would refute amenable-by-sofic permanence,
   which Arzhantseva–Berlai–Finn-Sell–Glebsky (arXiv:1802.04688, §4.4) record as open even for
   finite cyclic kernels, as quoted in `binary-jacobson-weak-sofic-status-proof`, Section 5.
   A nonsoficity proof for Radu's lattice therefore produces such a counterexample.
   *Status correction (ex2-radu-superstrong-negative, 2026-09-13).* The general permanence
   statement is already refuted. Kun–Thom Theorems A and E (`kun-thom-nonsofic-wreath`) give the
   nonsofic group `(Z/2)^(G/Γ) ⋊ G`, whose kernel is abelian and whose quotient `G` is residually
   finite. What stays open is the case of finite kernels, which `G_k` does not fall under. So the
   counterexample in this item would be a new mechanism without property (T), not the first
   counterexample.
4. **Screens.**
   * *Not residually finite.* For `k >= 2`, `G_k` is not residually finite. Every finite
     quotient of `G_k` is a finite quotient of `Γ_R`, so it kills `(xz)^4`. But `(xz)^2` is a
     primitive element of `Λ_v`, so `(xz)^4 ∉ γ_2(Λ_v)`.
   * *Not LEF.* For all large `k`, `G_k` is not LEF. Otherwise the finitely presented group
     `Γ_R`, a marked limit of LEF groups, would be LEF and hence residually finite.
   * *Split host for `k = 2`.* `G_2` embeds in `(C_1/B_1) ⋊ Q`, the 1-chains of
     `T_h × T_v/Λ_v` modulo boundaries of squares. The chain group `C_1` is a direct sum of
     permutation modules over `Q`.

So Radu's lattice sits inside the amenable-by-sofic permanence problem. Its soficity is equivalent
to soficity of all of the explicit groups `G_k`, whose kernels are free nilpotent and whose
quotient is one arithmetic lattice. Only the forward implication (2) is claimed.

Proof in `radu-lattice-is-limit-of-nilpotent-by-arithmetic-groups-proof`.
