---
rg: 2
id: sl3-fq-t-profinite-completion-is-finitely-presented
kind: claim
title: For r >= 3 and q >= 4 the profinite completion of SL_r(F_q[t]) is finitely presented as a profinite group
distinct_from:
  sl3-polynomial-covers-have-extra-finite-quotients: that is the open existence of finite quotients of the finitely presented covers in which the truncation kernel survives; this shows that the sufficient condition recorded there, non-finite presentation of the profinite completion, is false for q >= 4, and says nothing about the claim itself.
  kazhdan-cover-models-round-iff-kernel-fixed-mass-one: that is the rounding criterion for models pulled back from a Kazhdan cover, with a profinite corollary; this decides the profinite hypothesis of that corollary negatively at SL_r(F_q[t]).
artifacts:
  - research/artifacts/hl-hyperlinear-vs-sofic-2026-09-13.md
---

**ESTABLISHED** by `sl3-fq-t-profinite-completion-fp-proof`.

Let `q >= 4` be a prime power, `r >= 3`, and `Γ = SL_r(F_q[t])`. Then the
profinite completion `Γ^` is finitely presented as a profinite group. More
precisely

```text
Γ^  ≅  SL_r(F_q[[t]])  ×  SL_r(F_q[t,t^-1])^                              (PF1)
```

and both factors are finitely presented profinite groups.

**Reading.**
- Behr's failure of finite presentation of `SL_r(F_q[t])` is invisible in its
  profinite completion, as `sl3-polynomial-covers-have-extra-finite-quotients`
  suspected.
- So the sufficient condition "the profinite completion is not finitely
  presented" in the corollary of
  `kazhdan-cover-models-round-iff-kernel-fixed-mass-one` cannot be used at
  the Kun--Thom rank-3 vertex. Any instability proof through the rank-3
  covers must produce finite quotients of truncations that the profinite
  completion of `Γ` does not already force, i.e. it must show that no
  truncation has the same profinite completion as `Γ`
  (`fp-cover-truncations-see-kernel-iff-profinite-closures-differ`).
- The case `q in {2,3}` is not covered, because Theorem C of the import needs
  `q >= 4`.
