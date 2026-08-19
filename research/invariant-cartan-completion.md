---
rg: 2
id: invariant-cartan-completion
kind: claim
title: Invariant Cartan completion for the Kun–Thom Bernoulli pair
invalidates: [growing-fiber-models]
distinct_from:
  fiber-masa-free-cocycle: that asks to CONSTRUCT a model with no invariant masa; this asserts that every model has one — they are the two sides of the same coin and the graph should carry both
  coordinate-action-not-sofic: that is the imported Kun–Thom fact about the coset action; this is the missing lifting theorem which converts an abstract embedding into one to which that fact applies
artifacts:
  - notes/TRUE_DIAGONAL_NORMALIZER_RIGIDITY.md
---

Given a trace-preserving embedding `Θ : M_KT → ∏_𝒰 M_(d_n)`, prove that after
conjugation there is a **diagonal ultraproduct** `D_𝒰` with
`Θ(A_KT) ⊆ D_𝒰` and `Θ(u_g) D_𝒰 Θ(u_g)* = D_𝒰` for every `g ∈ G`.

**Establishing this refutes `hyperlinear-wreath-model`** and produces the
first non-hyperlinear group. By `diagonal-normalizer-rigidity` clause 4, an
invariant diagonal ultraproduct forces `Θ(u_g) ∈ 𝒮_𝒰 ⋉ U(D_𝒰)`, untwisting
plus free amplification then yields a Păunescu-sofic embedding, and
`coordinate-action-not-sofic` (Kun–Thom Corollary D) forbids one. Because the
containment half is free (abelian diagonalization), this claim is *equivalent*
to non-Connes-embeddability of `M_KT`, not merely sufficient for it.

## Two scope corrections worth carrying

1. **Diagonal, not merely maximal abelian.** The invariance must be asked of a
   *diagonal* ultraproduct `∏_𝒰 D_(d_n)`. An invariant masa of `∏_𝒰 M_(d_n)`
   that is not of that form yields no permutations: `diagonal-normalizer-rigidity`
   runs on the doubly stochastic matrix of `|u_ij|²` in a fixed matrix unit
   system, and a singular masa supplies none. So the constructive negation
   (`fiber-masa-free-cocycle` clause 3) only has to defeat diagonal
   ultraproducts, which is strictly easier than defeating all masas.
2. **Normalizers, not permutations.** No `Θ(u_g)` may even *normalize* such a
   `D_𝒰`; requiring them to be permutations is not needed. This is what
   `diagonal-normalizer-rigidity` clause 4 buys over the literal statement of
   Kun–Thom Definition 2.2, and it is what makes the negation the exact
   remaining freedom rather than an artefact of Păunescu's formulation.

## Why no cited result gives it

Kun–Thom start *inside* a permutation ultraproduct and prove a normalization
theorem there; they do not upgrade arbitrary unitary normalizers. The
Fourier-block calculation shows the upgrade cannot follow from abelianness or
from finite-dimensional simultaneous diagonalization alone: all possible
exoticity is stored in growing multiplicity fibers, which are invisible to the
lamp algebra and to the trace.
