---
rg: 2
id: bk-counterexample-trichotomy-proof
kind: route
title: Split on whether the radical is everything, a counterexample, or quasidiagonal, and read the third case through Brown-Dadarlat
target: bk-counterexample-trichotomy-via-qd-radical
requires:
  - stw07-separating-qd-quotients-force-quasidiagonality
  - stw07-qd-radical-criterion-compact-open
  - bk-no-compact-open-ideals-are-qd-invisible
  - brown-dadarlat-ext-trivial-class-gives-qd-extension
  - brown-dadarlat-qd-extensions-and-k0-hahn-banach
artifacts:
  - research/artifacts/bk-spectral-extension-permanence-2026-09-12.md
---

`E/R` is quasidiagonal by the radical theorem, so `R != 0`, since `E` is not
quasidiagonal.  The three cases `R = E`, `R` proper and not quasidiagonal, and
`R` quasidiagonal are exhaustive and mutually exclusive.  A quasidiagonal `R`
is proper.

**Case 2.**  `R` is separable and nuclear as an ideal of `E`, stably finite as
an ideal of a stably finite algebra, and not quasidiagonal.  So it is a
counterexample, and `stw07-qd-radical-criterion-compact-open` applies to it.

**Case 3.**  `R` is separable and quasidiagonal, hence σ-unital.  `E/R` is
separable, nuclear and quasidiagonal.  If `[γ^s] = 0`, Brown--Dadarlat
Proposition 2.5 would make `E` quasidiagonal.  If `ρ: R -> J` is an approximately
unital embedding into a quasidiagonal algebra with induced `η`, then
`E ↪ E(η)` (BD Definitions 2.4 and 3.1).  So `[η^s] = 0` would make `E` a
subalgebra of a quasidiagonal algebra.  Hence both classes are nonzero.

`Ext(K⊗E/R, K⊗R) ≅ KK^1(E/R, R)` for nuclear separable `E/R` (Kasparov).  If `R`
were KK-contractible this group would vanish.  `R ≅ R⊗W` would make `R`
KK-contractible, because `W` is KK-equivalent to `0`.  A compact-free spectrum
is excluded by `bk-no-compact-open-ideals-are-qd-invisible`.

UCT split.  If `E/R` satisfies the UCT, `E` is a stably finite extension of a
separable nuclear quasidiagonal UCT algebra by a separable nuclear
quasidiagonal ideal and is not quasidiagonal.  So it refutes
`blackadar-kirchberg-for-uct-quotient-extensions`.  By Moutzouris Remark 2.5
(recorded in `brown-dadarlat-qd-extensions-and-k0-hahn-banach`), `R` then lacks
the K_0-embedding property.  By Brown--Dadarlat Theorem 4.11 not every
separable nuclear quasidiagonal algebra has the K_0-Hahn--Banach property.
Otherwise `E/R` is a separable nuclear algebra outside the UCT class.

The compact traced ideal inside `R` is item 2 of
`stw07-qd-radical-criterion-compact-open`, applied to `E`.
