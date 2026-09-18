---
rg: 2
id: non-fp2-groups-are-quasi-retracts-of-simple-groups-proof
kind: route
title: Take the twisted Brin--Thompson group of the regular action; Alonso's theorem forces its finiteness down to that of H
target: non-fp2-groups-are-quasi-retracts-of-simple-groups
requires:
  - twisted-brin-thompson-groups-quasi-retract-onto-acting-group
---

Lane proof, 2026-09-18 (bh-free-17). Sources read at TeX source.
- Belk--Zaremsky, arXiv:2001.04579 (`twisted_Brin_Thompson.tex`):
  - l.153: `SV_G` is defined for any group `G` acting faithfully on a countable set `S`;
  - l.157, `thm:FinitelyGeneratedTheorem`: `SV_G` is finitely generated if and only if `G` is
    finitely generated and has finitely many orbits on `S`;
  - l.162 and l.164, `thm:quasi-retracts`: `ι_∅: G → SV_G` is a monomorphism, and when `G` and `SV_G`
    are finitely generated there is a coarse Lipschitz `ρ: SV_G → G` with `ρ ∘ ι_∅ = id`;
  - l.503, `thrm:simple`: `SV_G` is simple.
- LISW, arXiv:2510.01952v1 (`arxiv_v1.tex` l.591--599, Theorem 4.1): a quasi-retract of a group of
  type `F_n`, or of type `FP_n(R)` for a unital commutative ring `R ≠ 0`, is of the same type. LISW
  extend Alonso's `R = Z` case to all `R`.

**Proof.** Let `H` act on `S = H` by left multiplication. The action is faithful and transitive, and
`S` is countable.

1. By `thm:FinitelyGeneratedTheorem`, `SV_H` is finitely generated. By `thrm:simple`, it is simple.
2. `ι_∅(H) ≤ SV_H`, and by `thm:quasi-retracts` (the required node) `ρ` is a quasi-retraction onto
   `H`.
3. **Finiteness.**
   - `SV_H` is finitely generated, so it is of type `F_1` and `FP_1(R)` for every `R`. So is `H`.
   - Let `n ≥ 2` and `R ≠ 0`. If `SV_H` were of type `FP_n(R)`, then `H` would be of type `FP_n(R)`
     by LISW Theorem 4.1, hence of type `FP_2(R)`. Base change to a residue field `R/m` would then make
     `H` of type `FP_2(R/m)`: the kernels of a projective resolution are flat over `R`, so it stays
     exact after `⊗_R R/m`. That contradicts the hypothesis.
   - Type `F_n` (`n ≥ 2`) implies `FP_n(Z)`. Type `F` or `FP(R)` implies `FP_2(R)`. So neither group
     has any of the properties above length 1.

So `SV_H` and `H` have exactly the same finiteness properties. ∎

**What is new.** Only the bookkeeping. Belk--Zaremsky prove that every finitely generated group
quasi-isometrically embeds in a finitely generated simple group. Their proof gives a quasi-retraction
(l.167). The observation here is that when `H` has no finiteness beyond finite generation, nothing
else is needed for LISW's three conditions.
