---
rg: 2
id: ccr-hard-instance-subfactor-reducible
kind: claim
title: The Kazhdan copy is a reducible subalgebra in every nontrivial (CCR) instance
distinct_from:
  approximate-collapse-for-kt-compressor: that is the open (AC) wall itself — whether the congruence collapse survives approximate representations; this is an elementary structural observation about the same configuration, whose only role is to say which subfactor technology cannot be pointed at it.
  corona-commutant-no-growth: that is a growth statement about operator-norm relative commutants under the compression; this is the bare observation that the relative commutant is nontrivial to begin with, in the ultraproduct picture, and it makes no comparison between two commutants.
  kt-centralizer-normalization-hs: that is the full Hilbert-Schmidt normalization question; this is one hypothesis check inside it.
artifacts:
  - research/artifacts/hyperlinear-q34-literature-2026-08-18.md
  - research/kt-centralizer-normalization-hs.md
---

In the (CCR) configuration of `approximate-collapse-for-kt-compressor`: let
`σ = ∏_𝒰 π_n : G → U(M)` be trace-faithful into a tracial matrix
ultraproduct, `Λ = tΓt^{-1}` the compressed Kazhdan copy, `P = σ(Λ)'' ⊆ M`,
and `x ∈ σ(Λ)' ∩ M`.

**Claim.**  The instance is nontrivial exactly when `x ∉ ℂ1`, and then

```text
P' ∩ M ≠ ℂ1,
```

i.e. `P ⊆ M` is **not** irreducible.  Moreover the defect cannot be removed
by shrinking the subalgebra: `Q ⊆ P` implies `Q' ∩ M ⊇ P' ∩ M`, so every
subalgebra of `P` is reducible in `M` as well.

**What this prunes.**  Jeong's flattening theorem (`arXiv:2608.14487`)
characterises, for a subtracial completely positive `Φ : M → N` and an
**irreducible** `II₁` subfactor `P ⊆ M`, when `Φ` flattens under conjugation
by unitaries of `P`, the obstruction being a Pimsner--Popa inequality for
`E_P ∘ Φ^* ∘ Φ`, equivalently left weak mixing of an associated bimodule.
That is exactly the shape of tool the (CCR) lane has been looking for —
destroy correlations while keeping a rigid subgroup action — and its
hypothesis fails at precisely the instance where (CCR) becomes interesting.
A Jeong-style attack therefore needs a prior corner/fibre decomposition that
removes the relative commutant while retaining the compressor information;
without that step the theorem is unavailable, not merely hard to apply.

## Scope

Elementary; recorded as dead space, not as progress.  It does not say the
flattening idea is dead — only that the published theorem cannot be cited at
the hard instance as it stands — and it says nothing about the answer to
(AC).
