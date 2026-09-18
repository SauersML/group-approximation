---
rg: 2
id: perron-recovers-free-group-boundary-full-groups
kind: claim
title: The reduced-word boundary full group of a finitely generated free group is of type F-infinity by the Perron substitution theorem, with no power-and-phase recoding
requires:
  - perron-substitution-finiteness-for-garside-full-groups
---

**ESTABLISHED** (lane proof; a direct calibration of
`perron-substitution-finiteness-for-garside-full-groups`; not independently reviewed;
no priority claimed). It shows the Perron theorem applies where Li's `(t<d)` fails and
`raag-cube-codings-fail-li-multiplicity-at-every-power` had to recode.

## The coding

Let `F_k = ⟨a_1, …, a_k⟩`. Its boundary `∂F_k` is coded by the reduced-word automaton:
the deterministic category `𝔠` with one non-base object per generator-letter
`ℓ ∈ {a_1^±, …, a_k^±}` (the last letter written) plus the base `*`, and one atom
`ℓ → ℓ'` whenever `ℓ' ≠ ℓ^{-1}` (append `ℓ'`). Its boundary groupoid is the (amenable)
one-sided-tail groupoid of `∂F_k`, whose topological full group is a Higman--Thompson /
Nekrashevych-type group.

## The substitution matrix

On the `2k` letter-types, `M[ℓ', ℓ] = 1` iff `ℓ' ≠ ℓ^{-1}`, i.e. `M = J − P` where `J`
is all-ones and `P` is the fixed-point-free involution `ℓ ↔ ℓ^{-1}`.
- **Row sums** are `2k − 1`, so `M · 𝟙 = (2k−1) 𝟙`: Perron eigenvalue `λ = 2k − 1 > 1`,
  Perron vector `𝟙`.
- **Primitive:** `M[ℓ,ℓ] = 1` (append `ℓ` after `ℓ`), a self-loop, so aperiodic; and any
  `ℓ` reaches any `ℓ'` in `≤ 2` steps, so irreducible.
- **Diagonal is `1`**, so Li's `(t<d)` fails: from state `ℓ` only the single child `ℓ`
  returns to type `ℓ`. This is exactly the label-injective failure of
  `raag-cube-codings-fail-li-multiplicity-at-every-power`, here with `k` free letters.

## Conclusion

`M` is primitive with `λ = 2k−1 > 1`, so **(Perron)** holds. The unit groups are trivial
(deterministic automaton, `𝔠*(ℓ,ℓ) = 1`), hence of type `F_∞`. By
`perron-substitution-finiteness-for-garside-full-groups`, the boundary full group is of
type `F_∞`, and in particular finitely presented. `F_2 × F_2 = F_2 × F_2` is covered by
the product coding, whose substitution matrix is `M ⊗ I + I ⊗ M`-type with Perron
eigenvalue `(2·2−1)+(2·2−1) − …` positive `> 1` (the product of two primitive `λ>1`
matrices is primitive with product Perron eigenvalue `> 1`).

## Lesson for general BH

The free group is the smallest witness that recurrence in a Boone--Higman host is an
*off-diagonal* Perron phenomenon: a deterministic automaton with self-loop multiplicity
`1` is still loop-rich in the spectral sense (`λ = 2k−1`). The recoding that
`raag-cube-codings-fail-li-multiplicity-at-every-power` needed to force diagonal `≥ 2`
is unnecessary once finiteness is read off the Perron eigenvalue instead of the diagonal.
