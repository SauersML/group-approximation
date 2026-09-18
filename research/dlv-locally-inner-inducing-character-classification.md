---
rg: 2
id: dlv-locally-inner-inducing-character-classification
kind: claim
title: Dogon--Levit--Vigdorovich character classification over a locally inner inducing subgroup, with the finitary special linear rank decay and the generalised Bekka lemma
distinct_from:
  dudko-medynets-compressible-action-character-theorems: that imports character theorems for groups with compressible actions on topological spaces; this imports the locally-inner/inducing machinery for normal subgroups, the Bekka-type vanishing lemma and the rank decay of characters of SL_fin(F_q).
  dv-s-arithmetic-hs-stable-nonhyperlinear-extension: that imports a Hilbert--Schmidt stability theorem of Dogon--Vigdorovich for S-arithmetic groups; this imports the character-classification section of a different paper of Dogon--Levit--Vigdorovich.
  subshift-tower-unit-group-characters-are-constant: that proves constancy of characters on tensor-type unit group towers; this imports the corner-limit rank decay of nontrivial characters of SL_fin(F_q), where the Thoma--Skudlarek characters survive.
---

**ESTABLISHED by citation.** From A. Dogon, A. Levit and I. Vigdorovich, *Characters of diagonal
products and Hilbert--Schmidt stability*, arXiv:2407.11608 (v2). Conventions (their Section 5): a
*trace* of a countable group `G` is a normalized, positive-definite, conjugation-invariant function; `Tr(G)`
is the compact convex set of traces; `Ch(G)` is the set of its extreme points (*characters*). For
`psi in Tr(N)`, `N ◁ G`, the *trivial extension* `e psi` equals `psi` on `N` and `0` off `N`. The
commutator convention is `[g,x] = g^(-1) x^(-1) g x` (their proof of Lemma 5.10 uses
`phi(x^(-1) g x) = phi(g[g,x])`). Every trace is the barycenter of a unique Borel probability measure
on `Tr(G)` (pointwise topology, metrizable) that is carried by `Ch(G)` (Choquet--Thoma, quoted in Section 5).
The characteristic function `e 1_N` of `N ◁ G` is a character iff `G/N` is ICC; for `N = {e}` this says
`delta_e in Ch(G)` iff `G` is ICC.

1. **(Locally inner.)** A normal subgroup `N ◁ G` is *locally inner* if for every `g in G` and every
   finitely generated `F <= N` there is `h in N` with `g f g^(-1) = h f h^(-1)` for all `f in F`
   (Definition 2.7; the implementing element lies in `N`).
2. **(Restriction and extension.)** If `G` is countable and `N` is locally inner, then
   `Tr(N)^G = Tr(N)`, `phi in Ch(G)` implies `phi|_N in Ch(N)`, and `psi in Tr(N)` implies
   `e psi in Tr(G)` (Proposition 6.1).
3. **(Inducing.)** `N ◁ G` is *inducing* if every `phi in Ch(G)` with `N ∩ ker phi ⪇ N` vanishes on
   `G \ N`, where `ker phi = {g : phi(g) = 1}` (Definitions 6.2 and 5.2).
4. **(Classification, Theorem 6.4.)** If `N ◁ G` is a locally inner inducing subgroup of the countable
   group `G`, with `Q = G/N` and quotient map `p`, then the maps `f_1 : Ch(Q) -> Ch(G)`,
   `phi -> phi∘p`, and `f_2 : Ch(N) \ {1_N} -> Ch(G)`, `psi -> e psi`, are well defined, injective,
   have disjoint images, and `Ch(G) = Im(f_1) ∪ Im(f_2)`. So
   `Ch(G) ≅ (Ch(Q) ⊔ Ch(N))/(delta^Q_e ~ 1_N)` if `Q` is ICC, and
   `Ch(G) ≅ Ch(Q) ⊔ (Ch(N) \ {1_N})` otherwise, as topological spaces.
5. **(Extension of nontrivial characters, Proposition 6.3(1).)** Under the hypotheses of item 4, for
   every nontrivial `psi in Ch(N)` one has `e psi in Ch(G)`.
6. **(Generalised Bekka lemma, Lemma 5.10.)** If `phi in Tr(G)`, `g in G`, and `x_n in G` satisfy
   `lim_n phi([g,x_n]^(-1)[g,x_m]) = 0` for every `m`, then `phi(g) = 0`.
7. **(Rank decay, Proposition 8.5.)** Let `F = F_q` be a finite field and `SL_fin(F)` the group of
   finitary matrices over a countably infinite index set (entries differ from `delta_(i,j)` for only
   finitely many pairs). For every nontrivial `phi in Ch(SL_fin(F))`,
   `lim_n sup{|phi(g)| : rank(g - I) = n} = 0`.

**Also imported (countability).** Gorin--Kerov--Vershik, arXiv:1209.4945v3: for
`GL(∞,q)`, the inductive limit of `GL(n,q)` under the corner embeddings, "the set of extreme
(indecomposable) characters of GL(∞,q) is countable (see [Th72], [Sk])", the latter being
Skudlarek, Math. Ann. 223 (1976).

Verbatim text: [[dlv-locally-inner-inducing-character-classification-citation]].
