---
rg: 2
id: nowak-hamming-cubes-have-property-a-arbitrarily-badly-citation
kind: route
title: Import Nowak's diameter bounds for products of finite groups, as proved in Willett's notes on property A
target: nowak-hamming-cubes-have-property-a-arbitrarily-badly
requires: []
---

**Sources.**

- P. W. Nowak, *Coarsely embeddable metric spaces without Property A*, J. Funct. Anal. 252 (2007) 126–136
  (Theorems 3.3 and 4.3). The journal PDF was not reachable from this sandbox (the author's page returned HTML).
- R. Willett, *Some notes on property A*, arXiv:math/0612492v2. It reproves both of Nowak's theorems in full.
  The PDF was fetched on 2026-09-18 and read through `pypdf`. All quotes below are from it, with only the
  text-extraction spacing repaired.

**Verbatim (Definition 1.1.1, Yu's property A).** "A discrete metric space (X,d) has property A if for all
R,ε > 0, there exists a family {A_x}_{x∈X} of finite, non-empty subsets of X × N such that: for all x,y ∈ X
with d(x,y) ≤ R we have |A_x△A_y| / |A_x∩A_y| < ε; there exists S such that for each x ∈ X, if (y,n) ∈ A_x,
then d(x,y) ≤ S".

**Verbatim (Definition 1.2.2).** "a function x ↦ ξ_x from X to a Banach space will be said to have (R,ε)
variation if d(x,y) ≤ R implies ‖ξ_x − ξ_y‖ < ε."

**Verbatim (Theorem 1.2.4, condition 2).** "There exists p with 1 ≤ p < ∞ such that for all R,ε > 0 there
exists a map ξ : X → l1(X) such that: (a) ‖ξ_x‖_p = 1 for all x ∈ X; (b) ξ has (R,ε) variation; (c) there
exists S > 0 such that for each x, ξ_x is supported in B̄(x;S)."

**Verbatim (after Theorem 1.2.4).** "It is worth pointing out that of all these implications, only (8) ⇒ (9)
and (2) ⇒ (1) require the bounded geometry assumption." The proof of (1) ⇒ (2) sets
ξ_x(x′) = |({x′} × N) ∩ A_x| / |A_x|, which is nonnegative.

**Verbatim (Definitions 7.4.1).** "We define diam^A_X(R,ε) to be inf{S : supp ξ_x ⊆ B̄(e,S) for all x ∈ X where
ξ satisfies 1.2.4, (2)}, if this exists, and infinity otherwise." Also: "diam^F_G(R,ε) = inf{S : supp f ⊆
B̄(e,S), where f satisfies 6.1.1}". The "B̄(e,S)" in the first definition is a typo for B̄(x,S). That is the
support condition 1.2.4(2)(c), and it is how the proof of Proposition 7.4.5 uses it.

**Verbatim (Proposition 7.4.2).** "1. If X has property A then diam^A_X(R,ε) < ∞ for all R,ε > 0. 2. If X
is of bounded geometry, then it has A if and only if diam^A_X(R,ε) < ∞ for all R,ε > 0." The text before it
explains: "1.2.4 (2) is equivalent to property A in the bounded geometry case, and implied by it otherwise."

**Verbatim (Theorem 7.4.3, [Now07b] 3.3).** "Let G be a countable discrete amenable group, and fix R ≥ 1,
ε > 0. Then diam^A_G(R,ε) = diam^F_G(R,ε)".

**Verbatim (Theorem 7.4.4, [Now07b] 4.3).** "Let G be a non-trivial countable discrete group. Then for any
0 < ε < 2, lim inf_{n→∞} diam^F_{G^n}(1,ε) = ∞." Here G^n carries "the l1 metric, i.e.
d_{G×G}((g1,g2),(h1,h2)) = d_G(g1,h1) + d_G(g2,h2)", extended to n factors.

**Verbatim (the example).** "our sole ingredient is a finite group (even the two element group will do!)",
and: "The simplest example of this construction is given by Z2, the two element group. In this case, Z_2^n
with the l1 metric is (isometric to) the vertices of the edge graph of an n-dimensional cube, with metric
setting d(v,w) equal to the minimal number of edges joining v,w."

**Convention check.** Section 7.4 assumes that group metrics are integer-valued and "ha[ve] at least three
elements of norm at most one". For `Z_2^n` with the Hamming metric and `n ≥ 2`, the unit ball has `n + 1 ≥ 3`
elements. Theorem 7.4.3 is applied to `Z_2^n`, and the proof of Theorem 7.4.4 only needs an element of norm 1
in the factor `G`. Willett states explicitly that `G = Z_2` is allowed.
