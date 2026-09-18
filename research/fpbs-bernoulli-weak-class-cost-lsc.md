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

Non-free calibration of the diverging modulus (swarm-0917 wave 5, calibration). Dead. The aim
was to realise the anatomy (d) of `fpbs-bernoulli-class-cost-jump-is-cgdls-ultraproduct-gap` by
actual actions, dropping freeness of the approximants.

- *Construction.* Let Q_m = ⟨a,b | b a^m b^{-1} = a^m⟩, the HNN extension of ⟨a⟩ ≅ Z over
  ⟨a^m⟩ with trivial twist, and let π_m : F_2 = F(a,b) → Q_m be the quotient map. Let c_m be
  F_2 ↷ [0,1]^{Q_m} with product Lebesgue measure, acting through π_m by the Bernoulli shift.
- *Marked convergence.* Let w be freely reduced with |w| ≤ m+1 and π_m(w) = 1. If w contains
  b^{±1}, Britton's lemma gives a subword b^{±1} a^j b^{∓1} with m | j. Since w is freely
  reduced, j ≠ 0, so |w| ≥ m+2, a contradiction. Otherwise w = a^j, and ⟨a⟩ embeds, so
  j = 0. Hence ker π_m meets the ball of radius m+1 trivially, and Q_m → F_2 as marked groups.
- *Orbit-relation cost 1.* ⟨a^m⟩ is an infinite subgroup of Q_m, so the Bernoulli shift of
  Q_m restricted to it is mixing, hence ergodic. Fix a set A of measure ε. For a.e. x there is
  j with a^{mj}x ∈ A, and b x = a^{-mj} b a^{mj} x because a^m and b commute in Q_m. So the
  graphing {a, b|_A} generates R_{c_m}, and C(R_{c_m}) ≤ 1+ε. The b-edges are recovered only
  through routes of length ≥ m|j(x)|, so the moduli diverge exactly as in (d).
- *The limit is free and has cost 2.* Let γ ≠ 1. Once m ≥ |γ|, π_m(γ) ≠ 1 acts essentially
  freely, because Q_m is infinite. By CGdlS Lemma 2.43, μ_u(Fix γ) = lim_u μ(Fix_m γ) = 0, so
  c_u is essentially free. Its free standard factor from CGdlS Theorem 3.28 has the same cost.
  By Gaboriau (lecture notes, Corollary 2.25: "C_*(F_n) = C^*(F_n) = n"), that cost is 2. So
  lim_u C(R_{c_m}) = 1 < 2 = C(c_u) for the orbit-relation cost.
- *Where it dies.* The CGdlS cost of a non-free action is the groupoid cost C(G_{Γ↷X}), not
  the orbit-relation cost. Their Theorem 4.2 gives lim_u C(a_n) ≥ C_*(Γ) for every sequence of
  p.m.p. actions. For F_2 this forces lim_u C(G_{F_2↷X_m}) = 2 = C(c_u): no jump. The drop to
  1 comes only from forgetting the isotropy ker π_m, which a groupoid graphing must still
  generate. In general, no p.m.p. sequence, free or not, can go below C_*(Γ) in groupoid
  cost. A strict groupoid-cost jump at s̃ is a fixed-price counterexample, by the remark after
  CGdlS Question 4.3. So non-free actions calibrate nothing beyond the free case. Off the free
  locus, the orbit-relation cost is the wrong functional.
  Gaboriau source: *Around the orbit equivalence theory, measure equivalence, cost and
  L2-Betti numbers*, lecture notes, version of October 3, 2025,
  <https://perso.ens-lyon.fr/gaboriau/Travaux-Publi/ME-Cost-L2-Lectures/ME-Cost-L2-lectures.pdf>.
  Corollary 2.25 reads "The following groups are strongly treeable and have fixed price:
  C_*(F_n) = C^*(F_n) = n for the free group of rank n." Definition 2.9 defines C_* and C^* as
  the inf and the sup over free p.m.p. actions.
- *What would remain.* Non-free groupoid-cheap approximants a_n → s̃ would transfer to free
  ones via a_n × s, since C(a_n × s) ≤ C(G_{a_n}) by Abért–Weiss Theorem 9. That needs
  (a_n × s)~ → s̃. Approximating a partition of X_n × Y by rectangle partitions takes a number
  of pieces that is not uniform in n, so this continuity is not available, and I did not
  prove it.

Kazhdan local certificates (swarm-0917 wave 5). Dead at the same interchange. For Kazhdan Γ,
`fpbs-kazhdan-local-cost-formula` Theorem 1 bounds cost by a window-local defect D_{R,W}, which
is weak-star continuous only for a fixed window W. Suppose b_n → s̃ with C(b_n) ≤ C(s) − δ.
Near-optimal graphings of b_n give subgraphs G_n whose defect certificates need windows W_n.
If W_n stayed bounded along u, Corollary 2 applied to limit statistics would give C(s) ≤
C(s) − δ/2. By (d) of the gap node, W_n → ∞ along u. Passing to the ultralimit subgraph G_u on
b_u ≃ s only bounds the defect after the ultralimit, at unbounded windows. So the certificate
again needs W → ∞ to commute with lim_u, which is (c3) restated.

Soft-axiom obstruction (swarm-0917 wave 5). No proof from order-theoretic and topological
properties alone. Let T = {0} ∪ {1/n : n ≥ 1} and K = P(T) with the weak-star topology. Order K
by μ ≼ ν iff ν({t}) ≥ μ({t}) for every t ≠ 0. This order is closed, since each t ≠ 0 is
isolated in T. Put f(μ) = c − δ·μ(T∖{0}) with δ > 0. Then f is affine, and f is upper
semicontinuous because μ ↦ μ({0}) is upper semicontinuous. f is antitone for ≼, like cost
under weak containment, and δ_0 is the ≼-minimum with the maximal value c. But δ_{1/n} → δ_0
while f(δ_{1/n}) = c − δ. So a compact convex space with a closed order, a minimum, and an
affine, antitone, upper semicontinuous functional can still jump at the minimum. Any proof of
this claim must use an input specific to cost on F̃R, beyond compactness, affinity, Kechris
monotonicity and upper semicontinuity. The obvious candidates are freeness of the approximants
at every scale, or Γ-specific geometry.

Kesten gap at two-piece statistics (swarm-0917 wave 6, inverter;
`fpbs-bernoulli-class-approximants-are-almost-ergodic`, ESTABLISHED). This uses the Γ-specific
input named above. Let Γ be non-amenable and S generating, with κ = 2|S|(1−ρ). The Bernoulli
Koopman representation is ∞λ, so Σ_σ μ(BΔσB) ≥ κ p(1−p) for Bernoulli sets. The two-piece
matrices at a window F ⊇ S ∪ {e} carry this to every b within d of s̃ at (F,2), up to an error
(κ+4|S|)d. So approximants of s̃ expand every macroscopic set. Their invariant sets have mass
at most η or at least 1−η, with η ≤ 2(1+4|S|/κ)d. They have an ergodic component of mass at
least 1−η whose class is within 2η of b̃ at every window, and whose cost is at most
C(b)/(1−η). Consequences:

- This claim is equivalent to its restriction to free ergodic approximants.
- The cheap-approximability hole is equivalent to its ergodic version.
- A jump, if one exists, is realised by ergodic, uniformly almost-expanding e_n.
- Every approximant whose cheapness sits on a macroscopic piece with small S-boundary is killed,
  with an explicit lower bound on d. This covers invariant mixtures, non-ergodic sequences with
  macroscopic invariant mass, and cheap patches with small boundary.

**Where it stops.** This is a reduction, not (c3). It does not reach the soft-axiom example
above, whose jumping points δ_{1/n} are already extreme, so ergodicity alone is not the
missing input. It gives no bound on the coarse modulus. By
`fpbs-tight-routes-iff-bernoulli-weakly-treeable`, route moduli of near-minimizers diverge on
every non-treeable Γ even for the constant sequence, so an argument for (c3) must control
divergent moduli through expansion rather than bound them. The surviving question is whether
uniform almost expansion (A), combined with freeness, forces lim_u C_M(e_n) to be uniform in M.
