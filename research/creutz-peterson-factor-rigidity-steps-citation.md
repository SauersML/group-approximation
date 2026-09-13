---
rg: 2
id: creutz-peterson-factor-rigidity-steps-citation
kind: route
title: Quote the Creutz-Peterson lemmas, the proof of Theorem 5.4 and Proposition 6.1 from arXiv 1311.4513v3
target: creutz-peterson-factor-representation-rigidity-steps
requires: []
---

Source: arXiv:1311.4513v3 (22 Mar 2022; v1 18 Nov 2013). The e-print was fetched on MSI on
2026-09-13 and read in TeX (`creutzpeterson_revised2.tex`). Quotes below are verbatim, with
LaTeX turned into plain text. Numbering follows the section counters of that file: Section 4
holds `prop:freerestriction`, `thm:noembedding`, `lem:continuouscore`, `thm:smallcommutant`;
Section 5 holds `prop:commutantcontainment`, `lem:dlattice`, `lem:dcomm`,
`thm:amenablesubalgebra`, `cor:subgrouprigidity`; Section 6 holds `prop:oneTfactor`,
`prop:oneT`, `thm:oasuperrigidity1`, `thm:oasuperrigidity`, `cor:commensuratorfree` and the
final corollary. Caprace--Thom cite that final corollary as [CrePet2, Corollary 6.6].

**(CP-a) `lem:continuouscore`.** "Let G be a Polish group, suppose that Λ < G is a countable
dense subgroup such that any trace preserving ergodic action of G on a finite von Neumann
algebra is properly outer when restricted to Λ. Then for any representation π: Λ → U(M) into a
finite factor M, such that π(Λ)'' = M, the G-algebra of π is C." Its proof: "Let M_0 ⊂ M be the
G-algebra of π [...] If M_0 ≠ C, then by assumption we have that the action α restricted to Λ
is properly outer. [...] we must have E_0(π(λ)) = 0 for each λ ∈ Λ∖{e}. Since M = π(Λ)'' we
would then have M_0 = E_0(M) = C, giving a contradiction."

**(CP-b) `thm:smallcommutant`.** "Let G be a Polish group, and Λ < G a countable dense subgroup
such that each proper closed normal subgroup of G intersects trivially with Λ. Suppose G ↷
(Y, η) is ergodic, and π: Λ → U(M) is a representation into a finite factor such that M =
π(Λ)'', and such that the G-algebra with respect to π is C. If N ⊂ M is a von Neumann
subalgebra, and π does not extend to an isomorphism LΛ → M, then {σ⁰_λ ⊗ (J E_N(π(λ)) J) | λ ∈
Λ}' ∩ L^∞(Y, η) ⊗ B(L²N) = 1 ⊗ N."

**(CP-c) `thm:amenablesubalgebra`, statement:** "Suppose G is a locally compact group that is a
product of simple groups with the Howe-Moore property, and Λ < G is a countable dense subgroup
that contains and commensurates an irreducible lattice Γ < G, such that either (i) every
simple factor of G is connected; or (ii) G is simple and totally disconnected and Γ is
square-integrable and contains a nontorsion element. Suppose also that π: Λ → U(M) is a finite
factor representation such that π(Λ)'' = M, and set N = π(Γ)''. If π does not extend to an
isomorphism LΛ → M, then N is injective." **Proof, in full:** "If we take any Poisson boundary
(B, η) of G corresponding to a spread out probability measure on G, then G ↷ (B, η) is amenable
(Theorem 5.2 in [zimmeramenbound]) and contractive (Lemma 2.3 in [jaworski2]), and the
restriction to Γ is again amenable (Theorem 4.3.5 in [zimmerbook]) and contractive
(Proposition 2.4 in [creutzshalom]). Since Γ ↷ (B, η) is amenable, Theorem 5.1 in
[zimmerhyperfinite] shows that B_N is injective. By Proposition [prop:commutantcontainment],
we have that B_N ⊂ {σ⁰_λ ⊗ (J E_N(π(λ)) J) | λ ∈ Λ}', and so by combining Lemma
[lem:continuouscore], with Proposition [prop:freerestriction] (using Lemma [dcomm] in the
connected case) and Theorem [thm:smallcommutant], if π does not extend to an isomorphism LΛ →
M, then B_N ⊂ 1 ⊗ N, and hence 1 ⊗ N = B_N is then injective."
- `prop:commutantcontainment` assumes only: "G is a second countable locally compact group,
  and Γ < Λ < G where Γ < G is a lattice, and Λ < G is a countable dense subgroup that contains
  and commensurates Γ", with "G ↷ (B, η) a quasi-invariant action that is contractive when
  restricted to Γ".
- So the hypotheses (i)/(ii), the product structure and the Howe--Moore property enter the
  proof only through `prop:freerestriction`, whose conclusion is exactly the input of
  `lem:continuouscore`.

**(CP-d) `cor:subgrouprigidity`, proof:** "If π does not extend to an isomorphism LΛ → M, then
by Theorem [thm:amenablesubalgebra] we have that N is injective. Since G has property (T) so
does Γ [kazhdan], and hence it then follows from Theorem C in [robertson] that π(Γ) ⊂ U(N) is
precompact in the strong operator topology. Thus, it follows from the Peter-Weyl theorem that N
is isomorphic to a direct sum of matrix algebras."

**(CP-e) `prop:oneTfactor`.** "Suppose G is a second countable locally compact group, H ◁ G is
a closed normal subgroup, and Γ < G is a lattice such that the image of Γ is dense in G/H.
Suppose also that π: Γ → U(M) is a homomorphism into the unitary group of a finite factor M
such that π(Γ)'' = M. For any compact neighborhood of the identity U ⊂ G/H set Γ_U = {γ ∈ Γ | γH
∈ U}. If π(Γ_U) ⊂ U(M) is precompact in the strong operator topology for some compact
neighborhood of the identity U ⊂ G/H, then the G/H-algebra M_0 ⊂ M (with respect to the
quotient map Γ → G/H) has finite index in M." From its proof: "[...] it then follows that Z(N)
is finite dimensional and hence so is N. We set M_0 = N' ∩ M, which is then a finite index von
Neumann subalgebra of M. [...] we have shown that the finite index subalgebra M_0 ⊂ M is
contained in the G/H-algebra." The proof of `prop:oneT` ends: "by Proposition
[prop:freerestriction] and Lemma [lem:continuouscore] we must have M_0 = C, and hence M is
finite dimensional."

**(CP-f) `prop:freerestriction`, opening of the proof.** "Suppose g ∈ G, and v ∈ M_0 is such
that α_g(x) v = v x for all x ∈ M_0, then it follows that |v| ∈ Z(M_0) and so replacing v with
the partial isometry in its polar decomposition we may assume that v is a partial isometry, and
that v*v ∈ Z(M_0). We then have v = v v*v = v*v v, and so v*v ≥ v v*. As M_0 is finite we must
have v*v = vv*, and so [...] α_g(v*v) = v*v. Moreover, if q ∈ Z(M_0) such that q ≤ v*v = vv*
then we have α_g(q) = α_g(q) v v* = v q v* = q." Factor case: "Then since M_0 is a factor we
have v*v = 1, and so v is a unitary." The same proof, case (ii), non-factor branch: "Theorem 7.9
in [creutzpeterson] gives that the Λ-stabilizers are finite almost everywhere."

**(CP-g) Introduction.** "The space of characters forms a Choquet simplex, and the extreme
points correspond to representations that generate a finite factor [thoma1]."
