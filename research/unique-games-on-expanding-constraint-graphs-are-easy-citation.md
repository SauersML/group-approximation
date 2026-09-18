---
rg: 2
id: unique-games-on-expanding-constraint-graphs-are-easy-citation
kind: route
title: Import Theorems 1.1, 2.4, 2.6 and 3.2 of Arora--Khot--Kolla--Steurer--Tulsiani--Vishnoi, Unique Games on Expanding Constraint Graphs are Easy (STOC 2008)
target: unique-games-on-expanding-constraint-graphs-are-easy
requires: []
---

Literature import, credited in full.

Sanjeev Arora, Subhash A. Khot, Alexandra Kolla, David Steurer, Madhur
Tulsiani, Nisheeth K. Vishnoi, *Unique Games on Expanding Constraint Graphs are
Easy* [Extended Abstract], STOC'08, May 17--20, 2008, Victoria, British
Columbia, Canada (ACM 978-1-60558-047-0/08/05). The quotations below come from
text extracted from the extended-abstract PDF on 2026-09-17 by
`e-ugc-calibrate`. The extraction lost the spaces between words; they are
restored here, and mathematical symbols are transcribed (`η` for eta, `λ` for
lambda, `Λ` for a labeling).

* **Setting (Section 1).** The paper uses "the second smallest eigenvalue of the
  normalized Laplacian of a graph G, denoted by λ := λ_2(G)". The value of a
  labeling `Λ` is "the fraction of the constraints satisfied by it and is
  denoted by val(Λ)", and `opt(U)` is the maximum of `val(Λ)` over all labelings.
* **Theorem 1.1.** "There is a polynomial time algorithm for Unique Games that,
  given η > 0, distinguishes between the following two cases: YES case: There
  is a labeling which satisfies at least 1 − η fraction of the constraints. NO
  case: Every labeling satisfies less than 1 − O((η/λ) log(λ/η)) fraction of
  the constraints." The paper goes on: "An important feature of the algorithm is
  that its performance does not depend on the number of labels k."
* **Theorem 2.4 (implies Theorem 1.1).** "There is a polynomial time algorithm
  that computes a labeling Λ with val(Λ) ≥ 1 − O((η/λ) log(λ/η)) if the
  optimal value of the SDP in Figure 1 for U is 1 − η." The SDP in Figure 1
  maximizes `E_(e=(u,v) in E) E_(i in [k]) <u_i, v_(π_uv(i))>` subject to
  `E_i ||u_i||^2 = 1`, `<u_i, u_j> = 0` for `i != j`, and `<u_i, v_j> >= 0`.
  When all labels agree with a labeling it has value equal to that labeling's
  value, so its optimum is at least `opt(U)`.
* **Proof of Theorem 2.4.** "By Corollary 2.3 and Lemma 2.1, the labeling
  Λ_alg satisfies a 1 − O(tη/λ + 2^(−t/2)) fraction of the constraints of U.
  If we choose t to be an integer close to 2 log(λ/η), it follows that
  opt(U) ≥ 1 − O((η/λ) log(λ/η)). Since the rounding procedure R can easily
  be derandomized, a labeling Λ with val(Λ) ≥ 1 − O((η/λ) log(λ/η)) can be
  computed in polynomial time."
* **Rounding procedure R (Section 2.2).** "1. Pick a random vertex u. 2. Pick a
  label i for u from the distribution, where every label i' ∈ [k] has
  probability (1/k)||u_i'||^2. 3. Define Λ_alg(v) := σ_uv(i) for every vertex
  v ∈ V. (Of course, the rounding can be trivially derandomized since there are
  only nk choices for u, i.)" The procedure does not depend on `t`, which
  enters only in the analysis.
* **Corollary 2.3 (Local Corr. ⇒ Global Corr.).**
  "E_(u,v ∈ V)[ρ(u,v)] ≤ 2tη/λ + O(2^(−t/2))." Its proof begins: "We use the
  following characterization of λ for regular graphs G:
  λ = min E_((u,v) ∈ E) ||z_u − z_v||^2 / E_(u,v ∈ V) ||z_u − z_v||^2 (7)".
* **Theorem 2.6.** "Assuming UGC, for every η, δ > 0, there exists
  k = k(η, δ) such that for a Unique Games instance U = (G(V,E), [k], {π_uv})
  it is NP-hard to distinguish between YES Case: opt(U) ≥ 1 − η, NO Case:
  opt(U) ≤ δ and λ > Ω(η)." Proof sketch, Appendix A.3: "We show a reduction
  from this problem to the problem of distinguishing between Unique Games
  instances with value at least 1 − 2η and instances of value less than 2ε,
  under the additional promise of λ ≥ η/(1+η)."
* **Theorem 3.2.** "There is an algorithm that computes in time (kn)^(O(r)) a
  labeling Λ with val(Λ) ≥ 1 − O(ε/z_r(G)) if opt(U) ≥ 1 − ε and U has
  Γ-MAX2LIN form." Here `z_r(G)` is the optimum of a strengthened spectral
  relaxation of Sparsest Cut (Figure 2), with
  "λ ≤ z_1(G) ≤ ... ≤ z_n(G)".

**Reading of the import used downstream.** The `O(.)` in Theorem 2.4 is read as
one absolute constant `C_A >= 1`. The proof as quoted analyses the regular
case, through characterization (7). So the downstream claim applies the theorem
only to instances whose constraint graph is weighted-regular. The error term in
the quoted proof, `O(tη/λ + 2^(−t/2))`, only improves as `η` decreases. So the
guarantee holds with `η` replaced by any upper bound on the SDP error, and in
particular by `1 − opt(U)`.
