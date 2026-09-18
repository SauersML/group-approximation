---
rg: 2
id: bs1n-rq-padded-opnorm-stability-citation
kind: route
title: Import Willett's R_q-stability of the metabelian Baumslag--Solitar groups
target: bs1n-rq-padded-opnorm-stability
requires: []
---

Imported with credit, not reproved.  R. Willett, *Conditional representation
stability, classification of \*-homomorphisms, and relative eta invariants*,
arXiv:2408.13350, PDF dated May 25, 2026, read from arXiv on 2026-09-18.
Quotations are verbatim except that PDF-extraction glyph damage in formulas
(`p q` for parentheses, `´` for minus, `R q` for `R_q`) has been repaired.

Definition 1.3: "Let Γ be a discrete group, let S be a subset of Γ, and let
ϵ > 0. An (S,ϵ)-representation of Γ is a unital map π: Γ → B(H)_1 such that
‖π(s)π(t) − π(st)‖ < ϵ for all s,t ∈ S."

Definition 1.6: "The group Γ is Q-R-stable if for any finite subset S of Γ
and ϵ > 0 there exists a finite subset T of Γ and δ > 0 such that if
ϕ: Γ → M_n(C)_1 is a (T,δ)-representation, then there exists a map
θ: Γ → M_k(C) in Q(S,ϵ) and a representation π: Γ → M_{n+k}(C) in R such
that ‖(ϕ(s) ⊕ θ(s)) − π(s)‖ < ϵ for all s ∈ S. [...] If Q = R, we just say
that Γ is R-stable (conditional on P)."

Remark 1.8: "Specifically, the main case we will use is the class R_q of
finite-dimensional representations that factor through a finite quotient of
Γ, and Q = R = R_q."

Theorem 7.9: "Let Γ = ⟨S | r⟩ be a one-relator group, and F_S be the free
group on the generators of S. Assume moreover that Γ is torsion-free, LLP,
and FD. Then the following hold. (i) If r is not in the commutator subgroup
of F_S, then Γ is R_q-stable."

Example 7.11, displayed presentation (92): "BS(m,n) := ⟨a,b | b a^m b^{-1} =
a^n⟩", and its last paragraph: "The groups BS(1,n) are amenable and residually
finite, so our results also apply in that case: as the defining relation is
not in the commutator subgroup, these groups are R_q-stable."

Remark 1.13 (on the auxiliary summand in these theorems): "Theorem 1.10 gives
no control on the size of the auxiliary representation θ appearing in
Definition 1.6".

The presentation translation is Eilers--Shulman--Sorensen, *C\*-stability of
discrete groups*, arXiv:1808.06793v4, Proposition 2.16: "Let G be a finitely
presented discrete group. Then G is matricially stable if and only if the
following holds: For any ǫ > 0 there is δ > 0 such that for any
finite-dimensional C∗-algebra A and for any δ-almost homomorphism
f : S → U(A) there is a homomorphism π : G → U(A) such that
‖π(g) − f(g)‖ ≤ ǫ, for all g ∈ S."  The elementary word-evaluation argument
recorded in the target claim is used instead of this proposition for the
padded variant.

The open status of the unpadded case: same paper, Section 6, Question 3: "The
metabelian case n = 1, m > 1 is particularly interesting, and indeed the
structure of the associated C∗-algebra is rather well understood in this
case, cf. [Bre95, PV18]. We do not at present have any tools to address this
case."
