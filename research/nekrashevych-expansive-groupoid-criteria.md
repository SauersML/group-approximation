---
rg: 2
id: nekrashevych-expansive-groupoid-criteria
kind: claim
title: "Nekrashevych §5.1: compactly generated and expansive groupoids, the four-way criterion for expansive covers, invariance under transversal restriction, and expansive action groupoids are subshifts"
distinct_from:
  nekrashevych-symmetric-and-alternating-full-groups: that imports Definitions 3.1-3.2 and Theorems 4.1 and 5.6 of the same paper, read through a summarizing fetch, and says explicitly that the exact definition of an expansive groupoid still has to be read from the source; this imports that definition and the criteria of §5.1 verbatim from the TeX source.
---

**ESTABLISHED (import)** through `nekrashevych-expansive-groupoid-criteria-citation`.

Source: V. Nekrashevych, *Simple groups of dynamical origin*, arXiv:1511.08241, TeX source
`fullgr.tex`, Section 5.1 "Compactly generated and expansive groupoids". The quotes below
are copied from the TeX source. Only the macros are expanded: `\G` is `𝒢`, `\be` is the
source map `s`, `\en` is the range map `r`, `\X` is `𝒳`.

## Standing conventions (verbatim)

- "All groupoids in this paper are étale (see below) and the unit space `𝒢^{(0)}` is
  homeomorphic to the Cantor set."
- "A *`𝒢`-bisection* is a compact open subset `F ⊂ 𝒢` such that `s: F → s(F)` and
  `r: F → r(F)` are homeomorphisms. A topological groupoid `𝒢` is said to be *étale* if
  it has a basis of topology consisting of `𝒢`-bisections."
- Groupoid of an action, Example examp:action: "Its elements are multiplied according to
  the rule `(g_1, x_1)(g_2, x_2)=(g_1g_2, x_2)`, where the product is defined if and only
  if `g_2(x_2)=x_1`. We have `s(g, x)=x` and `r(g, x)=g(x)`."
- "A groupoid `𝒢` is said to be *minimal* if all its orbits are dense in `𝒢^{(0)}`."

## Imported statements (verbatim)

1. **Definition def:compactgenset.** "A groupoid `𝒢` is said to be *compactly generated*
   if there exists a compact set `S⊂𝒢` (called a *generating set*) such that
   `𝒢=⋃_{n≥1}(S∪S^{-1})^n`." Also: "Here `(S∪S^{-1})^n` is the set of products
   `γ_1γ_2⋯γ_n` such that `γ_i∈S∪S^{-1}`." And: "Suppose that `S` is a compact
   generating set of `𝒢`. Then any set `S_1⊇S` is also a generating set."
2. **Definition (expansive cover).** "Let `S` be an open compact generating set of `𝒢`. A
   finite cover `𝒮` of `S` by bisections is said to be *expansive* if the set
   `⋃_{n≥1}(𝒮∪𝒮^{-1})^n` is a basis of topology of `𝒢`."
3. **Proposition (independence of the cover).** "Suppose that there exists an expansive
   cover of a compact generating set of `𝒢`. Then for every compact generating set `S`
   of `𝒢` any finite cover `𝒮` of `S` by sufficiently small bisections is expansive."
4. **Proposition pr:bebasis.** "Suppose that `𝒮` is a finite cover by bisections of a
   compact generating set `S`. Denote, for `x∈𝒢^{(0)}` and `n≥1`, by `U_n(x)`
   intersection of all sets of the form `s(F)` containing `x`, for
   `F∈(𝒮∪𝒮^{-1})^k` and `k≤n`. Then the following conditions are equivalent.
   (1) The cover `𝒮` is expansive. (2) The sets `s(F)` for
   `F∈⋃_{n≥1}(𝒮∪𝒮^{-1})^n` form a basis of topology on `𝒢^{(0)}`. (3) For every two
   different units `x, y∈𝒢^{(0)}` there exist `A_1, A_2∈⋃_{n≥1}(𝒮∪𝒮^{-1})^n` such
   that `x∈s(A_1)`, `y∈s(A_2)`, and `s(A_1)∩s(A_2)=∅`. (4) For every `x∈𝒢^{(0)}` we
   have `⋂_{n≥1}U_n(x)={x}`."
5. **Proposition (transversals).** "Let `U⊂𝒢^{(0)}` be a clopen `𝒢`-transversal (i.e., a
   set intersecting every `𝒢`-orbit). Then the groupoid `𝒢|_U` is expansive if and only
   if `𝒢` is expansive."
6. **Proposition pr:expansivegroups.** "Let `G` be a finitely generated group acting by
   homeomorphisms on a Cantor set `𝒳`. Let `G×𝒳` be the groupoid of the action, and let
   `𝒢` be the groupoid of germs of the action. Then the following conditions are
   equivalent. (1) The groupoid `G×𝒳` is expansive. (2) The groupoid `𝒢` is expansive.
   (3) The action of `G` on `𝒳` is expansive, i.e., there exists a neighborhood
   `W⊂𝒳×𝒳` of the diagonal such that if `x, y∈𝒳` are such that `(g(x), g(y))∈W` for
   all `g∈G`, then `x=y`. (4) The dynamical system `(G, 𝒳)` is a subshift, i.e., there
   exists a finite set `X` and a `G`-equivariant homeomorphism between `𝒳` and a
   `G`-invariant closed subset of `X^G` (with the natural action of `G` on `X^G`)."
7. **Theorem th:finitelygenerated** (for context; it is Theorem 5.6 of the existing
   import node): "Suppose that `𝒢` is expansive and every `𝒢`-orbit has at least 5
   points. Then the group `alt(𝒢)` is finitely generated."

## Reading of "expansive groupoid"

The paper has no separate sentence defining an *expansive groupoid*. Items 5-7 use the
phrase for a compactly generated groupoid with an expansive cover (item 2) of some compact
open generating set. By item 3 this does not depend on the generating set. Consumers of
this node use exactly this reading:

> `𝒢` is **expansive** if it is compactly generated and some finite cover of some compact
> open generating set by bisections is expansive.

By item 4, the implication (3) ⇒ (1) applies to any finite cover by bisections of a
compact generating set.

**Verification level.** Items 1-6 and the conventions were read in the TeX source of
arXiv:1511.08241 (lines 787-982 of `fullgr.tex`), together with the proofs of items 3-5.
Item 6 was read with the first part of its proof.
