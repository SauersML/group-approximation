---
rg: 2
id: fpbs-bernoulli-class-approximants-are-almost-ergodic
kind: claim
title: Free actions close to the Bernoulli class in the space of weak-equivalence classes expand every macroscopic set with the Kesten constant and have one ergodic component of almost full mass, so both premises of the class-space route reduce to ergodic approximants
distinct_from:
  fpbs-bernoulli-class-cost-jump-is-cgdls-ultraproduct-gap: that identifies the ultraproduct cost along s̃-convergent sequences and reduces lower semicontinuity at s̃ to a uniform coarse modulus; this is a quantitative statement about each approximant at one finite window, using only the Kesten gap of the Bernoulli Koopman representation, and removes non-ergodic and macroscopically non-expanding approximants from both premises.
  fpbs-coinduced-dilution-needs-tempered: that constrains one family of approximants (co-induced dilutions) through fourth-moment-bounded Koopman vectors; this constrains every approximant through indicator functions at the window S with two pieces.
  fpbs-bernoulli-weak-class-cost-lsc: that is the open lower semicontinuity statement; this proves it is equivalent to its restriction to ergodic, uniformly almost-expanding approximants.
  fpbs-bernoulli-weak-class-cheap-approximability: that is the open approximation statement; this proves it is equivalent to its restriction to ergodic approximants.
---

**ESTABLISHED.** Let Γ be a non-amenable group with finite symmetric generating set S, let
ρ = ‖|S|^{−1} Σ_{s∈S} λ_Γ(s)‖ < 1 be its Kesten spectral radius, and put κ = 2|S|(1−ρ) > 0 and
c = 1 + 4|S|/κ. Let s be a nontrivial Bernoulli shift of Γ and (X,μ) standard non-atomic. Fix a
finite window F ⊂ Γ containing e and S, and for b ∈ A(Γ,X,μ) let

  d(b) = sup over Borel partitions (A, X∖A) of the max-norm distance from the matrix
         (μ(γ^b A_i ∩ A_j))_{γ∈F, i,j<2} to the set C_{F,2}(s).

So d(b) is at most the Hausdorff distance between C_{F,2}(b) and C_{F,2}(s), and d(b_n) → 0
whenever b̃_n → s̃ in the Abért–Elek topology.

**(A) Almost expansion.** For every Borel A ⊂ X, with t = μ(A),

  Σ_{s∈S} μ(A Δ s^b A) ≥ κ t(1−t) − (κ + 4|S|) d(b).

**(B) Almost ergodicity.** Every b-invariant Borel set has t(1−t) ≤ c·d(b). If c·d(b) < 2/9,
let η = η(b) ≤ 2c·d(b) be the smaller root of η(1−η) = c·d(b). Then η < 1/3 and there is a
b-invariant set A with μ(A) ≥ 1−η on which b is ergodic.

**(C) The big component is close to s̃.** If b is free and A is as in (B), the action e = b|_A
on (A, μ_A), μ_A = μ(·)/μ(A), is free and ergodic, and for all finite n, k,

  d_H(C_{n,k}(e), C_{n,k}(s)) ≤ d_H(C_{n,k}(b), C_{n,k}(s)) + 2η(b),

  C_{μ_A}(e) ≤ C_μ(b)/(1−η(b)).

**(D) Reductions.** Let Γ be non-amenable and finitely generated.

1. `fpbs-bernoulli-weak-class-cost-lsc` holds iff liminf_n C(e_n) ≥ C(s) for every sequence of
   free *ergodic* e_n with ẽ_n → s̃.
2. `fpbs-bernoulli-weak-class-cheap-approximability` holds iff s̃ is a limit of classes of free
   *ergodic* actions of cost arbitrarily close to C(Γ).
3. A cost jump at s̃, if one exists, can be realised by free ergodic e_n with ẽ_n → s̃,
   C(e_n) ≤ C(s) − δ, and the uniform almost expansion (A) with d(e_n) → 0.

For amenable Γ every free action is weakly equivalent to s, so (D) is vacuous there.

**What is killed.** Every approximant of s̃ whose cheapness is carried by a macroscopic
non-expanding piece. Precisely: if b has a Borel set A with μ(A) ∈ [η, 1−η] and
Σ_s μ(A Δ s^b A) ≤ τ < κ η(1−η), then d(b) ≥ (κη(1−η) − τ)/(κ + 4|S|), so b stays a fixed
distance from s̃ at the window (F, 2). This covers the invariant *convex mixtures*
t·a + (1−t)·s at fixed t (recorded in the Attempts of the cheap-approximability hole), every
non-ergodic sequence whose invariant sets have macroscopic mass, and every sequence built by
gluing a cheap structure on a region with small S-boundary. The invariant is the Kesten
constant κ of the Bernoulli Koopman representation. Every member dies at the two-piece
statistics at the window S.

The Attempts of `fpbs-bernoulli-weak-class-cost-lsc` record an unwritten reduction to ergodic
approximants for (T) groups, via Bauer simplices in the stable topology. (D) proves such a
reduction in F̃R for every non-amenable Γ. It uses no integral formula for cost and no
identification of representing measures.

Proof: `fpbs-bernoulli-class-approximants-are-almost-ergodic-proof`.
