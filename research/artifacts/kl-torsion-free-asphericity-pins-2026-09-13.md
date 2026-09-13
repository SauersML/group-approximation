# Torsion-free asphericity pins for the Kervaire--Laudenbach and Schur-kernel lanes (2026-09-13)

Lane solve-kervaire-laudenbach. The TeX sources were fetched on MSI from
`https://arxiv.org/e-print/<id>` into `~/kl-lane/`. The quotes below are
verbatim, up to TeX macros; line numbers refer to the fetched files.

## 1. Forester--Rourke, *Diagrams and the second homotopy group*, arXiv:math/0306088 (`pi-two.tex`)

Header l.124–127: title as above, authors Max Forester and Colin Rourke.

- **Main Theorem, l.174–186.** "Suppose that L=K∪e^1∪e^2 and that the attaching
  map for e^2 represents w in G*⟨t⟩ where G=π_1(K) and t is the new generator of
  π_1 determined by e^1. Suppose (1) G is torsion-free (2) the t–shape of w is
  amenable. Then there is an isomorphism of Zπ_1(L)–modules
  π_2(L) ≅ Zπ_1(L) ⊗_{Zπ_1(K)} π_2(K)."
- **l.193–195.** "Note that under conditions (1) and (2), Fenn and Rourke have
  solved the adjunction problem, and proved that π_1(K)→π_1(L) is injective [FR]."
- **l.202–203.** "However note that we do not need to assume that K is
  2–dimensional for our results."
- **Definitions, l.367–385.**
  - "The Magnus derivative D(T) is the t–shape given by deleting all subwords
    tt^{-1} and closing up."
  - "Call min{m | D^m(T) = t^q} the complexity of T and call D^{m-1}(T) the root
    of T."
  - "A one-clump shape is a t–shape which has exactly one clump which is not the
    whole shape. In other words it is a shape of the form t^p(tt^{-1})^q for
    p,q>0 or its inverse."
  - "A t–shape is amenable if it has root either tt^{-1} or a one-clump shape."
  - "It is easy to see that any t–shape of total exponent sum 1 in t is amenable
    since the root must be of the form t(tt^{-1})^q for q>0. On the other hand,
    no t–shape which is a proper power is amenable."
- **Example checked by hand.** `T = t t t t^-1` has one clump `t^3`, which is not
  the whole shape, so `T` is one-clump. `D(T) = t^2`, so `T` is its own root and
  `T` is amenable, with exponent sum 2.

## 2. Forester--Rourke, *The adjunction problem and a theorem of Serre*, arXiv:math/0412274 (`multi4.tex`)

Header l.28–29.

- **Theorem mainthm, l.98–106.** "Let (L,K) be a layered relative 2–complex with
  π_1(K) torsion-free. If the exponent matrix is invertible over Z then (a)
  π_1(K)→π_1(L) is injective, and (b) the inclusion-induced map
  Zπ_1(L) ⊗_{Zπ_1(K)} π_2(K) → π_2(L) is an isomorphism."
- **One layer.** One 1-cell and one 2-cell give a `1 x 1` exponent matrix, the
  exponent sum; it is invertible over `Z` exactly when it is `±1`.

## 3. Bogley--Edjvet--Williams, *Aspherical relative presentations all over again*, arXiv:1809.03460 (`BogleyEdjvetWilliams.tex`)

Header l.37: William A. Bogley, Martin Edjvet, Gerald Williams.

- **Lemma Covering, l.87–88.** "Suppose that (Y,X) is a relative two-complex
  where X and Y are connected CW complexes and the inclusion-induced
  homomorphism π_1X→π_1Y is injective. If π_2Y=0, then Y is aspherical if and
  only if X is aspherical."
- **Definition (l.96–97, paraphrased), then Lemma KG1, l.99–100.** P is
  aspherical when π_2(L(P),K(G,1)) = 0. "A relative presentation P=⟨G,x | r⟩ is
  aspherical if and only if the natural homomorphism G→G(P) is injective and
  L(P) is a K(G(P),1)-complex."
- **l.137.** "The asphericity status of a relative presentation … is unaffected
  if any relator r is replaced by a conjugate w r^ε w^{-1} …"
- **Lemma Coefficient, l.213–214.** "Given a relative presentation P=⟨G,x | r⟩,
  if H is any subgroup of G for which the set of relators r ⊆ G∗F is contained
  in the free product H∗F, then P is aspherical if and only if P_0=⟨H,x | r⟩ is
  aspherical."
- **Cellular model, l.79–83.** `L(P) = K ∨ ⋁_x S^1_x ∪ ⋃_r c^2_r` with
  `K = K(G,1)`. This is the complex of `aspherical-adjunction-has-zero-schur-kernel`.

## 4. Other sources read for this lane (no new node)

- **Klyachko--Thom, arXiv:1509.01376, l.107–110.** Gerstenhaber--Rothaus solve
  one-variable nonsingular equations *in* `U(n)`. "This property of solvability
  in a group is easily seen to pass to arbitrary Cartesian products of groups and
  arbitrary quotients of groups", hence to every subgroup of a quotient of
  `∏ U(n)`. Main already has the algebraic-quotient form in
  `nonsingular-adjunction-preserves-approximation-radicals`, so any bi-invariant
  metric on unitary groups is already covered.
- **Thom, arXiv:1712.01052.**
  - l.303: "Let G be a Lie group equipped with an bi-invariant metric generating
    its topology. If G is an abstract quotient of a product of finite groups, then
    G has abelian identity component."
  - Consequence for this lane: the degree argument cannot be carried into metric
    ultraproducts of finite groups through compact connected Lie groups.
    Kervaire--Laudenbach for weakly sofic groups stays unaddressed here.
- **Nitsche--Thom, arXiv:1811.07737, l.92–96.** Theorem
  `thm:gerstenhaber-rothaus`, as already imported on main.
