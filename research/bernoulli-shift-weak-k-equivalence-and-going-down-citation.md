---
rg: 2
id: bernoulli-shift-weak-k-equivalence-and-going-down-citation
kind: route
title: Chakraborty--Echterhoff--Kranz--Nishikawa Theorem 2.8, Bönicke--Dell'Aiera Theorem 4.6, and the generalized Green--Julg theorem quoted by Chabert--Echterhoff
target: bernoulli-shift-weak-k-equivalence-and-going-down
requires: []
---

**Sources.** Downloaded on MSI (`curl`), extracted with ghostscript `txtwrite`, read 2026-09-13. Quotes are verbatim
apart from typesetting.

**[CEKN]** S. Chakraborty, S. Echterhoff, J. Kranz, S. Nishikawa, *K-theory of non-commutative Bernoulli shifts*,
arXiv:2210.09209v1 (17 Oct 2022).
- **Definition 2.1.** "A morphism φ in KK^G(A,B) is a weak K-equivalence in KK^G if its restrictions to KK^H(A,B)
  induce isomorphisms K_*(A ⋊_r H) ≅ K_*(B ⋊_r H) for all finite subgroups H of G."
- **Definition 2.6.** "J^Z_{A_0,B} = ⊕_{F∈FIN(Z)} A_0^{⊗Z−F} ⊗ B^{⊗F}. [...] For A_0 = C, we just write J^Z_B = J^Z_{C,B}.
  Note that J^Z_{A_0,B} is a G-C_0(FIN(Z))-algebra in a natural way."
- **Theorem 2.8 (Theorem B).** "Let A, A_0 and B be C*-algebras with A and A_0 unital and let ι: A_0 → A be a unital
  *-homomorphism. Let φ ∈ KK(B,A) be an element such that ι⊕φ ∈ KK(A_0 ⊕ B, A) is a KK-equivalence. Then for each
  countable G-set Z, there is a weak K-equivalence in KK^G(J^Z_{A_0,B}, A^{⊗Z}). If G moreover satisfies BCC, there is
  an isomorphism [...]"
- **Proof of Theorem 2.8.** "When F is the empty set, we define Φ_F as the unital map ι^{⊗Z}: A_0^{⊗Z} → A^{⊗Z}."
- **Proof of Corollary 2.11.** "Let A = C({0,...,n}) and B = C({1,...,n}) and let φ: B → A be the canonical inclusion.
  The first isomorphism follows from Theorem 2.8."

The Baum--Connes hypothesis enters Theorem 2.8 only in its second sentence, through CEKN Theorem 2.3: "Suppose that the
Baum–Connes conjecture holds for G with coefficients in A and B. Then, any weak K-equivalence φ in KK^G(A,B) induces an
isomorphism K_*(A⋊_r G) ≅ K_*(B⋊_r G)."

**[BD]** C. Bönicke, C. Dell'Aiera, *Going-Down functors and the Künneth formula for crossed products by étale
groupoids*, arXiv:1810.04415, Trans. Amer. Math. Soc., doi:10.1090/tran/7913.
- **Setup.** "let S(G) be the set containing G and all of its compact open subgroupoids." "If F is a Going-Down
  functor for G, we define F^n(G) := lim_{X⊆E(G)} F^n_G(C_0(X)), where X runs through the G-compact subsets of E(G)."
- **Example 4.5.** "Let G be a second countable ample groupoid and A and B be separable G-algebras. Let F be the
  Going-Down functor defined by F*_H(C_0(X)) = KK^H_*(C_0(X), A|_H) and let G be the Going-Down functor defined by
  G*_H(C_0(X)) = KK^H_*(C_0(X), B|_H) as in Example 4.2. Suppose that x ∈ KK^G_*(A,B). Then we can define a Going-Down
  transformation Λ from F to G by letting Λ*_H(C_0(X)) be the map F*_H(C_0(X)) = KK^H_*(C_0(X), A|_H) → KK^H_*(C_0(X),
  B|_H) = G*_H(C_0(X)), · ⊗ x_H."
- **Theorem 4.6.** "Let F and G be two Going-Down functors for an ample groupoid G and let Λ be a Going-Down
  transformation between F and G. Suppose that Λ^n_H(C(H^(0))) : F^n_H(C(H^(0))) → G^n_H(C(H^(0))) is an isomorphism
  for all compact open subgroupoids H of G. Then Λ^n(G) : F^n(G) → G^n(G) is an isomorphism."

With the functors of Example 4.5, `F^n(G)` is `K^top_n(G; A)`. For a countable discrete group the compact open
subgroupoids are the finite subgroups and `C(H^(0)) = C`, so the hypothesis of Theorem 4.6 is that `x` restricts to
isomorphisms `KK^H(C, A) -> KK^H(C, B)`. Green--Julg identifies these with `K_*(A ⋊ H) -> K_*(B ⋊ H)` (context, not
re-read). This is item 2 of the target.

**[CE01]** J. Chabert, S. Echterhoff, *Permanence properties of the Baum-Connes conjecture*, Documenta Math. 6 (2001)
127--183.
- **Definition 1.6.** "A G-C*-algebra A is called a proper G-algebra, if there exists a proper G-space X and a
  non-degenerate G-equivariant homomorphism Φ : C_0(X) → ZM(A), the center of the multiplier algebra of A."
- **Introduction.** "Another application of the bijectivity of the induction homomorphism is given in [7], where it is
  shown that the generalized Green-Julg theorem (i.e., BCC for proper G-algebras) holds for all (second countable)
  locally compact groups G."
- **After Theorem 2.2.** "It also allows to prove the fact that the Baum-Connes assembly map µ_{G,A} : K^top_*(G;A) →
  K_*(A⋊_r G) is an isomorphism whenever A is a proper G-algebra, as is worked out in more detail in [7]."

Item 3 of the target is imported through these two statements; the paper [7] they cite was not re-read.
