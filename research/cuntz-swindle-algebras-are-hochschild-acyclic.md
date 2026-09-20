---
rg: 2
id: cuntz-swindle-algebras-are-hochschild-acyclic
kind: claim
title: An algebra with a Cuntz swindle endomorphism has vanishing Hochschild and cyclic homology in every degree, and no isometry of the relative commutant of its swindle image maps into the first Cuntz range
distinct_from:
  decidable-group-algebras-have-fp-central-simple-hosts: that is the host existence claim with a K-gate; this is an invariant any input-free swindle tensor factor for that gate must satisfy, stated for Hochschild and cyclic homology rather than K-theory.
  leavitt-algebra-hochschild-dimension-at-most-one: that bounds the projective dimension of L_2 as a bimodule; this concerns the Hochschild homology groups themselves of a swindle algebra, which must all vanish whatever its Hochschild dimension.
  ara-cortinas-leavitt-tensor-k-theory-vanishes: that gets K-triviality of B tensor L_2 for regular supercoherent B; this derives HH- and HC-acyclicity of every algebra carrying a swindle structure, with no regularity hypothesis.
---

**ESTABLISHED** by `cuntz-swindle-algebras-are-hochschild-acyclic-proof`
(swarm-0917-w20-w20-bh-pull, 2026-09-20; unreviewed). The only imports are two
textbook facts about Hochschild homology (Morita invariance through the
generalized trace, and triviality of inner automorphisms), both stated with
their chain-level formulas in the proof.

Let `k` be a field and `A` a unital `k`-algebra. A **Cuntz swindle structure** on `A` is:
- `s_1, s_2, s_1^*, s_2^* ∈ A` with `s_i^* s_j = δ_ij` and `s_1 s_1^* + s_2 s_2^* = 1`;
- a unital `k`-algebra endomorphism `σ` of `A` with
  `σ(a) = s_1 a s_1^* + s_2 σ(a) s_2^*` for every `a ∈ A`. (S)

This is the structure asked for by the swindle-factor lane
(`fp-central-simple-cuntz-swindle-algebra-exists` on the live bus, not yet in
this tree). Suppose `A` carries such a structure.

1. **Hochschild acyclicity.** `HH_n(A) = 0` and `HC_n(A) = 0` for every `n ≥ 0`.
   The same holds for `D ⊗_k A` and for `M_r(D ⊗_k A)`, for every unital `k`-algebra `D`.
2. **Intertwiners.** `s_1 a = σ(a) s_1` and `s_2 σ(a) = σ(a) s_2`, `s_2^* σ(a) = σ(a) s_2^*`
   for all `a`. So `s_2, s_2^*` and `e = s_1 s_1^*` lie in the relative commutant
   `R = σ(A)' ∩ A`, and `1 ~ 1 − e` inside `R`.
3. **Commutant no-go.** Suppose the centre of `A` has no idempotents other than `0, 1`
   (for instance `A` simple). Then there are no `v, v^* ∈ R` with `v^* v = 1` and
   `e v v^* = v v^*`. That is, `1` is not subequivalent to `e` inside `R`, although
   `1 ~ e` in `A` through `s_1`, and `[e] = 0` in `K_0(R)`.

## What this kills, and where

- *Invariant:* `HH_*` (and `HC_*`) over `k`. Every candidate factor with a nonzero
  Hochschild class in any degree dies at the additivity step
  `HH(σ) = HH(id) + HH(σ)`. By item 1 this is stronger than the trace test
  (`HH_0 = 0`) and needs no auxiliary coefficient ring such as `k[ε]`.
- *Tensor decompositions die.* By Künneth over a field, `HH_*(A_1 ⊗ A_2) =
  HH_*(A_1) ⊗ HH_*(A_2)`. So a swindle factor cannot be assembled as a tensor
  product of algebras each having some nonzero Hochschild class. This covers every
  product of Leavitt path algebras with Cantor crossed products whose Hochschild
  homology is nonzero; see the conditional list in the proof route.
- *Commutant models die at item 3.* Any construction in which the swindle is
  implemented by structure commuting with `σ(A)`, so that an isometry of `R` carries
  `1` into the range of `s_1`, forces `σ` to be inner. A swindle endomorphism of a
  nonzero algebra is never inner (Step 5 of the proof, with no hypothesis on the centre). In the
  model `V ≅ V ⊗ W` with `σ = (−) ⊗ 1_W`, the range of `s_1` must be finite relative
  to the part of `1 ⊗ End(W)` that lies in `A`.

Scope: this does not decide whether a finitely presented central simple swindle
algebra exists. It sharpens what such an algebra must look like: HH-acyclic, with
`R` containing the isometry `s_2` onto `1 − e` but no isometry into `e`.
