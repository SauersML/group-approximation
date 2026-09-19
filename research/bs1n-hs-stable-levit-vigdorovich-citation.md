---
rg: 2
id: bs1n-hs-stable-levit-vigdorovich-citation
kind: route
title: Import Levit--Vigdorovich Corollary D(3), their HS-stability definition, and Lemma 3.5
target: bs1n-hs-stable-levit-vigdorovich
requires: []
---

Imported with credit, not reproved.  A. Levit and I. Vigdorovich,
*Characters of solvable groups, Hilbert--Schmidt stability and dense periodic
measures*, arXiv:2206.02268, PDF read from arXiv on 2026-09-19 with `pypdf`.
The quotations are verbatim.  Only PDF-extraction damage is repaired: the
ligature `ﬁ` becomes `fi`, and broken spaces inside words are rejoined.

Introduction, p. 1: "A discrete group G is called Hilbert–Schmidt stable if
every “almost homomorphism” of G into a finite-dimensional unitary group is
“nearby” an actual homomorphism with respect to the Hilbert–Schmidt metric.
The formal definition is outlined in §9."

§9, (9.1): "normalized Hilbert–Schmidt norm on the group U(n) is
‖A‖HS = √((1/n) tr(A∗A)) ∀A∈ U(n)."

§9, Definition: "Let G be a discrete group. An asymptotic homomorphism of the
group G is a sequence of set-theoretic maps fn : G→ U(n) for all n∈ N
satisfying (9.4) dHS(fn(g)fn(h), fn(gh)) → 0 ∀g,h∈G.  The group G is
Hilbert–Schmidt stable if for any asymptotic homomorphism fn : G→ U(n) there
is a sequence of group homomorphisms ϕn : G→ U(n) such that (9.5)
dHS(fn(g), ϕn(g)) → 0 ∀g∈G."

Note that `phi_n` takes values in the same `U(n)` as `f_n`: there is no padding.

p. 3: "Corollary D. The following metabelian groups are Hilbert–Schmidt
stable: [...] (3) The Baumslag–Solitar groups BS(1,n) for all non-zero n∈ Z."

Proof of Corollary D, (3), p. 34: "The Baumslag–Solitar group BS(1,n) is
isomorphic to Z ⋉ Z[1/n]. The Pontryagin dual of the abelian group Z[1/n] is
the n-adic solenoid Sn and the dual action corresponds to multiplication by n.
The dynamical system (Z, Sn) has dense periodic measures by Proposition 8.7.
We conclude relying on Proposition 10.2."

p. 14: "Lemma 3.5 (Bekka–de la Harpe). Let N be an abelian normal subgroup of
the group G with Pontryagin dual N̂. Let ϕ∈ Tr(G) be a trace whose restriction
to N corresponds to the Borel probability measure µϕ ∈ Prob(N̂) via the
Fourier transform. Then ϕ(g) = 0 for every element g∈ G that acts
µϕ-essentially freely on N̂."

The proof there cites [BdlH20, Theorem 12.D.1], which treats exactly
`G = Z ⋉ Z[1/n]` with `N = Z[1/n]`.

The corollary in the target node (a trace that is Dirac on `Z[1/2]` is regular)
is deduced there in five lines from Lemma 3.5.
