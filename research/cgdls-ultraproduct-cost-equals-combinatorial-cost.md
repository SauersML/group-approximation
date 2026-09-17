---
rg: 2
id: cgdls-ultraproduct-cost-equals-combinatorial-cost
kind: claim
title: The cost of an ultraproduct of actions equals the combinatorial cost of the sequence, is attained by a free standard weakly equivalent factor, and dominates the limit of the costs
distinct_from:
  burton-kechris-cost-usc-and-maximum-action: that imports upper semicontinuity of cost on free actions and on free weak-equivalence classes; this imports the ultraproduct identity C(a_u) = cC_u((a_n)n), the standard factor theorem, and the open Question 4.3 on strictness of C(a_u) ≥ lim_u C(a_n).
  cost-is-constant-on-weak-equivalence-classes: that imports monotonicity of cost under weak containment for standard free actions; this imports the cost theory of non-standard ultraproduct groupoids and their standard factors.
---

**ESTABLISHED (import).** Let Γ be a finitely generated group and u a non-principal ultrafilter
on N. For p.m.p. actions a_n : Γ ↷ (X_n, μ_n), let a_u be the ultraproduct action on the Loeb
space (X_u, μ_u). Let cC_u((a_n)n) be the u-combinatorial cost of the graphed groupoids
(G_{Γ↷X_n}, S) for a finite generating set S.

1. (Theorem 2.29) Measurable sets of X_u are internal up to null sets, and internal sets have
   measure equal to the u-limit of the measures.
2. (Lemma 2.43) Standard groupoids are realizable, and so are ultraproducts of realizable
   graphed groupoids. Fixed-point sets pass to the ultraproduct: Fix([φ_n]_u) = [Fix(φ_n)]_u up
   to null sets.
3. (Definitions 3.8 and 3.11) C_M(G, Φ) is the infimum of the costs of graphings M-coarsely
   equivalent to Φ, and cC_u((G_n, Φ_n)n) = inf_{M ∈ N^N} lim_{n∈u} C_M(G_n, Φ_n).
4. (Theorem 3.28) Every graphed p.m.p. groupoid has a standard factor that is weakly
   equivalent to it, has the same cost, and is measurably free. If the groupoid is realizable,
   the factor is free.
5. (Theorem 4.2) C(a_u) = cC_u((a_n)n) ≥ lim_u C(a_n). If a_u is essentially free, then
   C^*(Γ) ≥ C(a_u), where C^*(Γ) is the supremum of costs of free p.m.p. actions.
6. (Question 4.3, open) Can C(a_u) ≥ lim_u C(a_n) be strict for some finitely generated Γ?

**Source.** A. Carderi, D. Gaboriau, M. de la Salle, *Non-standard limits of graphs and some
orbit equivalence invariants*, arXiv:1812.00704v3 (20 Jan 2021), Annales Henri Lebesgue 4
(2021). Read 2026-09-17 from the arXiv PDF. Line breaks and notation are normalised: a_u for
a_u, C^* for the supremum cost.

- Theorem 2.29: "For every n ∈ N let (Xn,µn) be a probability space and let Xu be the
  ultraproduct of the sequence (Xn)n. Then there exists a probability measure µu on Xu such
  that 1. for every sequence of measurable subsets (An ⊂ Xn)n the set [An]u is µu-measurable
  and µu([An]u) = lim n∈u µn(An), 2. for every µu-measurable subset Au ⊂ Xu there exists a
  sequence of measurable sets (An ⊂ Xn)n such that µu(Au∆[An]u) = 0."
- Lemma 2.42: "Every p.m.p. groupoid on a standard Borel probability space is realizable."
- Lemma 2.43: "The ultraproduct (Gu, Φu) of a sequence of realizable graphed p.m.p. groupoids
  (Gn, Φn) is itself realizable. Moreover every bisection ϕu = [ϕn]u satisfies up to null sets
  [FixBn(ϕn)]u = [Fix(ϕn)]u = Fix(ϕu) = FixBu(ϕu) and [MF(ϕn)]u = MF[(ϕn)]u."
- Definition 3.8 (end): "The M-coarse cost of the graphed groupoid (G, Φ) is defined as the
  infimum of the costs of all graphings of G which are M-coarsely equivalent to Φ,
  CM(G, Φ) := inf{C(Ψ) : Ψ ∼c_M Φ}."
- Definition 3.11: "Let (Gn, Φn)n be a sequence of graphed p.m.p. groupoids. The
  u-combinatorial cost of the sequence is cCu((Gn, Φn)n) := inf M∈N^N lim n∈u CM(Gn, Φn)."
- Theorem 3.28: "(Standard factor). Every graphed p.m.p. groupoid (G, Φ) over any probability
  space (X, B, µ) admits some p.m.p. factor (G′, Φ′) on a standard Borel probability space
  such that: 1. (G′, Φ′) is weakly-equivalent to (G, Φ); 2. the pull-back graphing of Φ′ is Φ;
  3. C(G) = C(G′) (even when C(Φ) = ∞); 4. the factor G → G′ is measurably free. Moreover if G
  is realizable, then the factor is free."
- Section 4: "If a : Γ ↷ X is a p.m.p. Γ-action, we denote by C(a) and call it the cost of the
  action the cost of the p.m.p. groupoid GΓ↷X. Similarly for a sequence of Γ-actions
  an : Γ ↷ Xn, we denote by cCu(an) the combinatorial cost of the sequence of graphed groupoids
  (GΓ↷Xn, S) for any generating subset S < Γ (this is independent of the choice of S by
  definition, see Definition 3.11)."
- Section 4: "by C^∗(Γ) the supremum cost (i.e., the supremum of the costs of the free p.m.p.
  actions of Γ). It is realized by any Bernoulli shift action of Γ (Abért-Weiss [AW13])."
- Theorem 4.2: "Let Γ be a finitely generated group. For every sequence (an)n of p.m.p.
  Γ-actions we have: C(au) = cCu((an)n) ≥ lim u C(an) ≥ lim inf n→∞ C(an) ≥ C∗(Γ). (23)
  Moreover if the action au is essentially free we have C^∗(Γ) ≥ C(au) and hence if Γ has
  fixed price we obtain lim u C(an) = cCu((an)n) = C(au) = C∗(Γ)."
- Question 4.3: "Can the inequality C(au) ≥ lim u C(an) in Theorem 4.2 be strict for some
  finitely generated group Γ? Observe that such an example would provide an example to the
  fixed price problem (whether there are countable groups for which C∗(Γ) ≠ C^∗(Γ) [Gab00,
  Question I.8])."

**Reading of item 4 for actions.** For Γ ↷ X_u with graphing S, the pull-back graphing of Φ′
is S, so Φ′ consists of the images of the generators. A free factor of the action groupoid is
therefore the action groupoid of an essentially free p.m.p. Γ-action on a standard space,
which is a factor of a_u. CGdlS use it this way in the proof of their Corollary 4.6: "The same
holds for any of its (measurably free) weak equivalent standard factors (given by Theorem
3.28) which thus has finite stabilizers."
