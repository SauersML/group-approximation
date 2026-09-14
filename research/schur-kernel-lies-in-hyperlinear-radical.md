---
rg: 2
id: schur-kernel-lies-in-hyperlinear-radical
kind: claim
title: The Schur kernel of a nonsingular adjunction lands in the hyperlinear radical of every central extension
distinct_from:
  nonsingular-adjunction-preserves-approximation-radicals: that bounds the coefficient kernel of one adjunction inside the approximation radicals of the coefficient group itself; this places the image of second-homology classes killed by the adjunction of the quotient in the hyperlinear radical of an arbitrary central extension, where no coefficient need die.
  mf-hyperlinear-radical-divergence: that separates the MF radical from the hyperlinear radical of one group; this produces central elements of hyperlinear radicals from a homological kernel and says nothing about MF radicals.
artifacts:
  - research/artifacts/kl-schur-kernel-central-extensions-2026-09-11.md
---

Let `E` be countable, `1 -> Z -> E -> Q -> 1` central with class `alpha`,
and `alpha_H : H_2(Q; Z) -> Z` its universal-coefficient evaluation. For
every nonsingular `w in Q * <t>`,

    alpha_H( K_2(Q, w) )  <=  Rad_hyp(E).

**Consequences.**

* If any countable `Q` and nonsingular `w` have `K_2(Q, w) != 0`, some
  countable group is not hyperlinear: take a central extension by `Q/Z` whose
  multiplier detects a killed class. This holds even when `Q` is residually
  finite, and no Kervaire--Laudenbach failure is needed.
* For Deligne's triple cover `E_3` of `Sp_4(Z)`, a nonsingular equation over
  `Sp_4(Z)` whose Schur kernel meets the mod-three multiplier puts the central
  mark in `Rad_hyp(E_3)`. That is (DCM1) of `deligne-central-mark-hs-collapse`.

DERIVATION
schur-kernel-hyperlinear-radical-proof
