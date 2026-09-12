---
rg: 2
id: deligne-cocycle-has-rank-approximate-projective-representations
kind: claim
title: Deligne's mod-three multiplier on Sp4(Z) has rank-approximate projective representations in every characteristic other than three
refuted_by:
  - deligne-twisted-group-algebra-is-not-stably-finite
distinct_from:
  maslov-mod3-projective-defect-gap: that asserts a uniform positive normalized Hilbert--Schmidt defect for unitary projective almost representations; this asks for vanishing normalized-rank defect for invertible matrices over finite fields of characteristic p != 3, a different metric over different fields.
artifacts:
  - research/artifacts/deligne-twisted-group-algebras-2026-09-12.md
---

**OPEN.** For every prime `p != 3`, the multiplier `w^a` of Deligne's triple cover `E_3` of `Gamma = Sp_4(Z)`
has rank-approximate projective representations in characteristic `p`. That means: for every finite
`B <= Gamma` and `eps > 0` there are a finite field `F` of characteristic `p` containing `w` and
`rho : B -> GL_d(F)` with `rank(rho(g)rho(h) - w^(a(g,h)) rho(gh)) <= eps d` whenever `g, h, gh in B`.

**Payoff.**
- **Linear soficity.** By `deligne-cover-linear-soficity-is-rank-projective-approximation`, this is exactly
  `F_p`-linear soficity of `E_3` for every `p != 3`.
- **Stable finiteness.** Together with the characteristic-three theorem, it gives
  `deligne-triple-cover-group-algebras-are-stably-finite`, so `E_3` carries no strict linear automaton over any
  finite field.

## Attempts

- **Exact or bounded-dimension models: dead.** The twisted group algebras have no nonzero finite-dimensional
  module (artifact Lemma 1.1, from Deligne's finite residual and Malcev). Over finite fields, bounded `d` with
  `eps < 1/d` would be exact, so models need growing dimension and a genuine defect.
- **Truncating a monomial twisted module along coordinate Folner sets: dead**
  (`deligne-monomial-twisted-modules-have-no-folner-truncations`).
  - Property (T) of `Sp_4(Z)` forces a finite orbit.
  - Finite abelianization of finite-index subgroups of `E_3` then gives a finite quotient separating `z`.
  - Twisted induced modules over every subgroup are included.
- **Non-monomial subspace truncations of one exact module: open.**
  - Property (T) gives no rank rounding over finite fields
    (`kazhdan-group-rank-models-admit-no-expander-decomposition`, where `EL_3(F_2[t])` has rank-Folner
    truncations of its polynomial module).
  - So nothing kills this route by (T).
  - The module could not be locally finite (Lemma 1.1).
  - No twisted module of `Sp_4(Z)` in characteristic `p` with slow-growth filtrations is known.
- **Through soficity: open.** Sofic `E_3` would give this at every `p`
  (`sofic-implies-linear-sofic-over-every-field`), and `deligne-triple-cover-is-sofic` is open.
- **Through hyperlinearity:** no transfer is known. Unitary HS projective almost representations
  (`deligne-sector-gap-is-exactly-nonhyperlinearity`) are not rank models over finite fields.
