---
rg: 2
id: fpbs-bernoulli-class-cost-jump-is-cgdls-ultraproduct-gap
kind: claim
title: Along free actions converging to the Bernoulli class the ultraproduct has Bernoulli cost, so lower semicontinuity at s̃ is equivalent to a uniform coarse modulus and to a negative answer to CGdlS Question 4.3 there
distinct_from:
  fpbs-bernoulli-weak-class-cost-lsc: that is the open lower semicontinuity statement; this proves the ultraproduct identity C(b_u) = cC_u = C(s), the unconditional lower semicontinuity of every fixed-modulus cost at s̃, and the equivalence of the open statement with a uniform coarse modulus and with non-strictness in CGdlS Question 4.3 along s̃-convergent sequences.
  fpbs-weak-topology-cost-lsc-envelope-is-group-cost: that is the barrier in the weak topology of actions; this works on the space of free weak-equivalence classes and locates the remaining content in the interchange of inf over coarse moduli with the ultralimit.
  cgdls-ultraproduct-cost-equals-combinatorial-cost: that imports C(a_u) = cC_u ≥ lim_u C(a_n) for arbitrary sequences; this computes both sides when the sequence converges to the Bernoulli class.
---

**ESTABLISHED.** Let Γ be an infinite finitely generated group with finite generating set S,
s a nontrivial Bernoulli shift of Γ, and (X,μ) standard non-atomic. Let b_n ∈ FR(Γ,X,μ) with
b̃_n → s̃ in F̃R(Γ,X,μ), let u be a non-principal ultrafilter on N, and let b_u = ∏_n b_n/u.
For M ∈ N^N write C_M(b) = C_M(G_{Γ↷X}, S), as in Definition 3.8 of CGdlS.

(a) **Ultraproduct cost.** b_u is essentially free and C(b_u) = cC_u((b_n)n) = C(s).

(b) **Fixed modulus is automatic.** For every M ∈ N^N, lim_{n∈u} C_M(b_n) ≥ C(s). Since u is
    arbitrary, liminf_n C_M(b_n) ≥ C(s). So every fixed-modulus cost b ↦ C_M(b) is lower
    semicontinuous at s̃, with no hypothesis on Γ.

(c) **Equivalences.** The following are equivalent.
    1. `fpbs-bernoulli-weak-class-cost-lsc`: liminf_n C(b_n) ≥ C(s) for all such sequences.
    2. *Negative answer to CGdlS Question 4.3 at s̃*: C(b_u) = lim_u C(b_n) for all such
       sequences and all u.
    3. *Uniform coarse modulus*: for all such sequences, all u and all ε > 0, there is
       M ∈ N^N with lim_u C_M(b_n) ≤ lim_u C(b_n) + ε.

(d) **Anatomy of a cost jump.** Suppose lim_u C(b_n) = C(s) − δ with δ > 0. Then for every
    M ∈ N^N and every η < δ, for u-almost every n no graphing Ψ of b_n with
    C(Ψ) ≤ C(b_n) + η is M-coarsely equivalent to S. A counterexample to
    `fpbs-bernoulli-weak-class-cost-lsc` is exactly a sequence converging to s̃ whose
    near-optimal graphings need coarse moduli, relative to the Cayley graphing S, that diverge
    along u.

**Consequence for the route.** With `fpbs-bernoulli-lower-bound-from-weak-class-lsc-approximation`,
the Bernoulli lower bound C(a) ≥ C(s) for all free a is equivalent to (c3) together with
`fpbs-bernoulli-weak-class-cheap-approximability`. If cheap approximability holds and fixed price
fails, then (c) gives a sequence converging to s̃ with a strict inequality in Question 4.3.

**What is killed.** Arguments that bound C_M, or any witness of fixed window and route length,
along a sequence converging to s̃ prove nothing new: by (b) such bounds hold for every Γ. A
proof of `fpbs-bernoulli-weak-class-cost-lsc` must control how the coarse modulus of
near-optimal graphings grows along the sequence, which is (c3). A disproof must build
sequences with diverging moduli, which is (d). The informal window-divergence description in
the target's ## Attempts is now a theorem, with the modulus made precise by CGdlS
Definition 3.8.

Proof: `fpbs-bernoulli-class-cost-jump-is-cgdls-ultraproduct-gap-proof`.
