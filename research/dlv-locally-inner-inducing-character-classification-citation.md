---
rg: 2
id: dlv-locally-inner-inducing-character-classification-citation
kind: route
title: Import the locally inner and inducing subgroup theorems, the Bekka-type lemma and the SL_fin rank decay of Dogon--Levit--Vigdorovich verbatim
target: dlv-locally-inner-inducing-character-classification
requires: []
---

**Source.** A. Dogon, A. Levit, I. Vigdorovich, *Characters of diagonal products and Hilbert--Schmidt
stability*, arXiv:2407.11608v2, PDF fetched from arxiv.org and read on 2026-09-18. Quoted verbatim
(ligatures and line breaks normalized):

- **Section 5 (conventions).** "The space of all traces on the group G is denoted by Tr (G)." "The
  extreme points of the convex set Tr (G) are called characters. That is, characters are traces that
  cannot be written as a proper convex combination of traces. We denote by Ch (G) the space of
  characters of the group G." A trace is required to be positive-definite, normalized (`φ(e) = 1`) and
  conjugation-invariant. "Any trace φ∈ Tr (G) arises as the barycenter of a unique Borel probability
  measure µφ on Tr (G) satisfying µφ(Ch (G)) = 1, see [Tho64b]." Tr(G) carries "the topology of
  pointwise convergence" and, "As the group G is countable, the space Tr (G) is metrizable."
- **Trivial extension (Section 5).** "Let ψ∈ Tr (N) be any trace. The trivial extension of ψ to the group
  G is given by eψ :G→C, g ↦ ψ(g) ∀g∈N, 0 ∀g∉N." And: "The trivial extension e1N is a character of the
  group G if and only if the quotient group Q =G/N has the ICC property".
- **Definition 2.7.** "An automorphism σ of a group G is locally inner if for any finitely generated
  subgroup F≤G there is some element h∈G such that σ(g) =g^h for all g∈F . An action of a group H on a
  group G by automorphisms is locally inner if each element of H is acting via a locally inner
  automorphism. A normal subgroup N◁G is called a locally inner subgroup if the conjugation action of
  the group G on N is locally inner." The text continues: "the conjugation action of G on its normal
  subgroup N is required to be locally inner from the “point of view” of N."
- **Definition 5.2.** "The kernel of the trace φ∈Tr(G) is ker φ ={g∈G : φ(g) = 1}. The trace φ is
  called faithful if ker φ ={e}. φ is called trivial if ker φ =G so that φ≡1."
- **Lemma 5.10 (Generalised Bekka lemma).** "Consider a trace φ∈ Tr (G). Fix an element g∈G. If there
  is a sequence of elements x_n∈G such that lim_{n→∞} φ([g,x_n]^{-1}[g,x_m]) = 0 for every m∈N then
  φ(g) = 0." Its proof uses "φ(g) = lim_n φ(x_n^{-1} g x_n) = lim_n φ(g[g,x_n])", which fixes
  `[g,x] = g^{-1}x^{-1}gx`.
- **Proposition 6.1.** "Let G be a countable group and N a locally inner subgroup of G. Then (1) Tr
  (N)^G = Tr (N). (2) If φ∈ Ch (G) then φ|_N∈ Ch (N). (3) If ψ∈ Tr (N) then eψ∈ Tr (G)."
- **Definition 6.2.** "A normal subgroup N◁G is called inducing (respectively weakly inducing) if every
  character φ∈ Ch (G) such that N∩ ker φ ⪇ N (respectively [N :N∩ ker φ] =∞) satisfies φ(g) = 0 for
  all g∈G\N."
- **Proposition 6.3.** "Let G be a countable group and N a locally inner subgroup of G. Let ψ∈ Ch (N)
  be a character. Assume either that (1) N is inducing and ψ is non-trivial, or (2) N is weakly
  inducing and [N : ker ψ] =∞. Then the trivial extension of ψ satisfies eψ∈ Ch (G)."
- **Theorem 6.4.** "Let N◁G be a locally inner inducing subgroup with quotient group Q =G/N. If the
  quotient group Q is ICC then Ch (G)≅ (Ch (Q)⊔ Ch (N))/(δ^Q_e ∼ 1_N). If the quotient group Q is not
  ICC then Ch (G)≅ Ch (Q)⊔ (Ch (N)\{1_N}). These identifications are understood in the sense of
  topological spaces." Its proof: "the map f1 : Ch (Q)→ Ch (G), f1 :φ↦φ◦p is well-defined by
  Proposition 5.4. Furthermore, it follows from the assumptions together with Proposition 6.3 that the
  map f2 : Ch (N)\{1_N}→ Ch (G), f2 :ψ↦ eψ is also well-defined. The two maps f1 and f2 are
  injective and satisfy Im(f1)∩ Im(f2) =∅. It follows from Item (2) of Proposition 6.1 that Ch (G) =
  Im(f1)∪Im(f2)."
- **Section 8 setup.** "Let p be a prime. Fix the finite field F =F_q for some q =p^k and k∈N." "We
  remind the reader that for us, characters are always extremal as a point in Tr(G) and normalized so
  that φ(e) = 1."
- **Finitary groups.** "Let SLfin (F ) denote the direct limit of the special linear groups SLn(F ) as
  n tends to infinity. Alternatively, we may view the group SLfin (F ) as consisting of finitary
  matrices over a countably infinite index set. This means that the entries g_{i,j} of each matrix
  g∈ SLfin (F ) differ from δ_{i,j} only for finitely many pairs of indices i and j."
- **Proposition 8.5.** "Let φ∈ Ch (SLfin (F )) be any non-trivial character. Then lim_n sup{|φ(g)| :
  g∈ SLfin (F ), rank(g− I) =n} = 0." The paper adds: "Alternatively, Proposition 8.5 can be deduced
  quite directly from the character classification of the group SLfin (F ) available in [Sku76]."

**Second source.** V. Gorin, S. Kerov, A. Vershik, *Finite traces and representations of the group of
infinite matrices over a finite field*, arXiv:1209.4945v3, read on 2026-09-18: "Realize GL(n,q) as a
subgroup of GL(n+1,q) acting in the space spanned by the first n coordinate vectors and fixing n+1st
coordinate vector and consider the inductive limit of GL(n,q) with respect to such embeddings. In this
way we get the infinite-dimensional group GL(∞,q). However, the representation theory of GL(∞,q)
turns out to be not as rich as one could hope for. For instance, the set of extreme (indecomposable)
characters of GL(∞,q) is countable (see [Th72], [Sk])".

Items 1--7 and the countability statement of the claim restate these quotes. Nothing is re-proved
here. ∎
