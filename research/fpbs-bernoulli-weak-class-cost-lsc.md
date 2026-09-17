---
rg: 2
id: fpbs-bernoulli-weak-class-cost-lsc
kind: claim
title: Cost is lower semicontinuous at the Bernoulli weak-equivalence class in the space of free weak-equivalence classes
distinct_from:
  fpbs-weak-topology-cost-lsc-envelope-is-group-cost: that shows lower semicontinuity at s in the weak topology of actions is fixed price itself; this is lower semicontinuity at s̃ in the finer-quotient space F̃R of classes, where singleton classes are closed and the condition is a priori weaker.
  fpbs-bernoulli-weak-class-cheap-approximability: that asks whether cheap classes accumulate at s̃; this asks whether cost can jump down in the limit at s̃.
---

**OPEN.** Let Γ be an infinite finitely generated group, s a nontrivial Bernoulli shift of Γ,
and F̃R(Γ,X,μ) the compact metrizable space of free weak-equivalence classes (Abért–Elek
topology). Then for every sequence of free actions a_n with ã_n → s̃ in F̃R,

    liminf_n C(a_n) ≥ C(s).

Cost on F̃R is upper semicontinuous (`burton-kechris-cost-usc-and-maximum-action`, item 5), so
this is equivalent to continuity of cost at the single point s̃. It is the s̃ instance of
Burton–Kechris Problem 10.14, which asks for continuity at every point of F̃R.

It is necessary for fixed price: if C ≡ C(Γ) on FR, the inequality is trivial. A failure is a
*cost jump at the Bernoulli class*: free actions whose statistics converge to Bernoulli
statistics but which keep cheap generating graphings, with the cheapness witnessed only in
windows that escape to infinity.

## Attempts

Uniformise Kechris's upper semicontinuity witness. The witness that C(a) < r is a finite family
of sets and partial translations. The generators are reproduced by words in them outside an
error set, and the error is paid for by extra graphing pieces. Its validity is an open
condition on finitely many statistics of a, which is why cost is upper semicontinuous.
Transferring the witness of C(a_n) < r to s requires the window and the slack to be uniform in
n. Hausdorff convergence of statistics sets is only for each fixed window, so the transfer
dies at exactly the uniformity step. A counterexample to this claim is precisely a sequence
whose minimal witness windows diverge. This is the same mechanism as the connectivity loss in
`fpbs-dead-limit-graphing-connectivity`.

Reduction to ergodic approximants for property (T), not written as a proof. Burton–Kechris
Theorem 10.31 (Burton–Tucker-Drob) makes the stable class space F̃R_s a Bauer simplex when Γ
has (T). Cost is a stable weak-equivalence invariant for finitely generated Γ, since
C(i_Γ × a) = C(a), and it is affine under convex combination. If moreover cost satisfies the
barycentric formula over the Bauer representing measure, then approximants of the extreme
point s̃_s have representing measures concentrating near s̃_s. That would reduce this claim,
for (T) groups and in the stable topology, to ergodic approximants a_n. Missing input: the
identification of the representing measure with the pushforward of the ergodic decomposition,
imported verbatim, and the matching integral formula for cost.

Ultraproduct reformulation (swarm-0917, stability-approximation). This turns the uniformisation
attempt above into theorems, in `fpbs-bernoulli-class-cost-jump-is-cgdls-ultraproduct-gap`.

- *Ultraproduct cost.* Let b_n be free with b̃_n → s̃ and u non-principal. By Burton–Kechris
  Theorem 10.2, the ultraproduct b_u is ≃ s. It is essentially free by CGdlS Lemma 2.43, and
  its free standard factor from CGdlS Theorem 3.28 is ≃ s. So C(b_u) = cC_u((b_n)n) = C(s).
- *Fixed moduli.* For every fixed coarse modulus M, liminf C_M(b_n) ≥ C(s) holds for every
  finitely generated Γ.
- *Equivalence.* This claim is equivalent to the uniform coarse modulus (c3) of that node:
  near-optimal graphings of b_n can be taken M-coarsely equivalent to S with M independent of n
  along u. It is also equivalent to C(b_u) = lim_u C(b_n) for every s̃-convergent sequence,
  which is the s̃ case of CGdlS Question 4.3.

What dies. Every argument that transfers witnesses of a fixed window or fixed route length
already gets only what (b) gives unconditionally. Where it stops: I found no mechanism that
bounds the coarse modulus of near-optimal graphings of b_n uniformly in n. Lemma 3.6 of CGdlS
gives a modulus depending on the action. A cost jump needs graphings whose S-route lengths
diverge along u, and I could neither build such a sequence nor exclude one.
