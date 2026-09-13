---
rg: 2
id: blsw-real-lattice-frobenius-stability-citation
kind: route
title: Import Bader--Lubotzky--Sauer--Weinberger Theorems 1.1(F), 1.3, 2.10, 2.11 and Corollaries 1.4, 2.14
target: blsw-real-lattice-frobenius-stability
requires: []
---

Citation import. On 2026-09-13 the PDF of arXiv:2303.08943v2 (30 Aug 2023) was
fetched on MSI into `/scratch.global/sauer354/ex/ex-nh-deligne-hs/blsw.pdf` and
pages 1--16 were read. U. Bader, A. Lubotzky, R. Sauer, S. Weinberger,
*Stability and instability of lattices in semisimple groups*, J. Anal. Math.
151 (2023), no. 1, 1--23; the journal data is from reference [3] of
Bachner--Dogon--Lubotzky, arXiv:2508.17392v3.

Verbatim, page by page.

- **p. 2, Theorem 1.1.** "Let Γ be a finitely generated group. (F) [19] If
  H^2(Γ, V) = 0 for every unitary representation of Γ on any Hilbert space V,
  then Γ is Frobenius stable." Reference [19] is De Chiffre--Glebsky--Lubotzky--Thom.
- **p. 2, (F).** "The Frobenius norm (the L^2-norm), i.e., for A ∈ M_n(C),
  ||A||_F = tr(A^*A)". The square root is evidently intended, since it is called
  the L^2-norm.
- **p. 3, Definition 1.2.** "A group Γ has property [T_n] if its cohomology
  H^i(Γ, V) vanishes for every unitary Γ-representation V and every 1 ≤ i ≤ n.
  It has property (T_n) if this holds provided V has no non-zero Γ-invariant
  vectors."
- **p. 3.** "[5] ... shows that an irreducible lattice Γ in a higher rank
  semisimple Lie group G has property (T_{n−1}) where n is the minimal rank of
  each non-compact factor of G [5, Theorem E]." Reference [5] is Bader--Sauer.
- **p. 3.** "the group G = Sp(2g, R) has a universal central extension G~ with
  an infinite abelian kernel which implies that H^2_c(G, R) and H^2(Γ, R) are
  non-zero. So Γ does not have property [T_2] despite having property (T_2)."
- **p. 3, Theorem 1.3.** "Let G be a real semisimple Lie group and Γ < G be an
  irreducible lattice. We assume that each non-compact factor of G has rank at
  least 3. Then Γ is Frobenius stable with the possible exception that one of the
  non-compact factors is of Hermitian type and Γ does not have the congruence
  subgroup property."
- **p. 3--4.** CSP "has been proved in most cases, in particular G = Sp(2g, R),
  see [31, Theorem 3]." Also: "these lattices are never Hilbert-Schmidt stable.
  Recall that the Hilbert-Schmidt norm is nothing more than the renormalization
  of Frobenius norm, i.e. ||A||_HS = n^{−1/2} ||A||_F for A ∈ M_n(C)."
- **p. 4, Corollary 1.4.** "Let G = Sp(2g, R), g ≥ 3, and let G~ its universal
  central extension. For every lattice Γ < G, in particular for Γ = Sp(2g, Z),
  the preimage Γ~ of Γ in G~ is not Frobenius approximated."
- **p. 13, Theorem 2.10.** "Let G be a semisimple Lie group with finite center
  and no compact factors. Let Γ < G be a lattice. Denote by G~ → G the universal
  cover and let Γ~ → Γ be the pull back of Γ. If all simple factors of G are of
  real rank at least 3 then G and Γ have property (T_2) and G~ and Γ~ have
  property [T_2]."
- **p. 13--14, Theorem 2.11 (Deligne).** "Let Γ < G be a lattice satisfying the
  congruence subgroup property. Assume that π_1(G) is infinite. Let G~ → G be
  the universal cover, which is the universal central extension of G. Then the
  preimage Γ~ is not residually finite. Furthermore, PR(Γ~) ⊂ ker(Γ~ → Γ) is a
  subgroup of finite index."
- **p. 15, Corollary 2.14.** "Let Γ be a finitely generated group and let
  N ◁ Γ be a normal subgroup such that Γ/N is finitely presented. Assume that
  the intersection of N with the profinite radical of Γ is of finite index in N.
  If Γ is Frobenius stable then also Γ/N is Frobenius stable."
- **p. 15, proof of Theorem 1.3.** "We denote Γ~ = π^{−1}(Γ). By Theorem 2.10,
  Γ~ is a [T_2]-group and by Theorem 1.1 it is Frobenius stable. We let N ◁ Γ~
  be the kernel of the extension Γ~ → Γ. By Corollary 2.14, if the intersection
  of N with the profinite kernel of Γ~ is of finite index in N then Γ is
  Frobenius stable."
- **p. 1.** "in case Γ = <S | R> is a finitely presented group defined by a
  finite set of generators S and a finite set of relations R, Γ is g-stable iff
  for every ε > 0 there exists δ > 0 such that for every n and for every map
  ρ : S → G_n, if for every word w = s_1 ··· s_m in R, d_n(ρ(s_1)···ρ(s_m), 1_{G_n})
  < δ then there exists a group homomorphism ρ~ : Γ → G_n such that for every
  s in S, d_n(ρ(s), ρ~(s)) < ε".

Used at statement level. The proofs are not re-derived here.
