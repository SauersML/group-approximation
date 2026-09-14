---
rg: 2
id: fp-cover-truncations-see-kernel-iff-profinite-closures-differ
kind: claim
title: A truncation kernel survives in a finite quotient exactly when the truncation's profinite completion differs from the limit group's
distinct_from:
  kazhdan-cover-models-round-iff-kernel-fixed-mass-one: that decides rounding of pulled-back models by the kernel's fixed mass and states a profinite sufficient condition; this is the exact profinite equivalent of its finite-quotient hypothesis, together with its monotonicity in the truncation index.
  sl3-fq-t-profinite-completion-is-finitely-presented: that computes the profinite completion of SL_r(F_q[t]) and shows it is finitely presented; this is a general statement about truncations of any group, with no arithmetic input.
artifacts:
  - research/artifacts/hl-hyperlinear-vs-sofic-2026-09-13.md
---

**ESTABLISHED** by `fp-cover-truncations-profinite-closure-proof`.

Let `Γ~` be a finitely generated group, `N ◁ Γ~`, and
`N_1 <= N_2 <= ...` normal subgroups of `Γ~` with `∪_L N_L = N`. Put
`Γ = Γ~/N`, `Γ_L = Γ~/N_L` and `K_L = N/N_L <= Γ_L`. Write `cl(M)` for the
closure of `M` in the profinite completion `Γ~^`.

1. `K_L` survives in some finite quotient of `Γ_L` (some homomorphism from
   `Γ_L` to a finite group is nontrivial on `K_L`) if and only if
   `cl(N_L) ≠ cl(N)`.
2. If `K_(L+1)` survives in a finite quotient of `Γ_(L+1)`, then `K_L`
   survives in a finite quotient of `Γ_L`. So "for infinitely many `L`" and
   "for every `L`" are the same condition.
3. `K_L` survives in no finite quotient of `Γ_L` if and only if the natural
   map `Γ_L^ -> Γ^` is an isomorphism.

**Consequence for the rank-3 vertex.**
`sl3-polynomial-covers-have-extra-finite-quotients` holds for a given
finitely presented Kazhdan cover and enumeration if and only if no truncation
`Γ_L` has the same profinite completion as `SL_3(F_q[t])`. For `q >= 4` that
completion is finitely presented as a profinite group
(`sl3-fq-t-profinite-completion-is-finitely-presented`), so a presentation-
counting argument at the profinite level cannot supply the survivors.
