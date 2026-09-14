---
rg: 2
id: fp-group-of-intermediate-growth-exists
kind: claim
title: A finitely presented group of intermediate growth exists
---

**OPEN.** Grigorchuk's question: is there a finitely presented group whose growth function is
neither polynomial nor exponential?

Source (Grigorchuk, *Milnor's problem on the growth of groups and its consequences*,
arXiv:1111.0512, TeX source read on MSI; pins in
`research/artifacts/fp-intermediate-growth-pins-2026-09-13.md`): "All known examples of groups of
intermediate growth are infinitely presented groups", followed by Problem `finitepresent`: "Is it
true that the growth function of a finitely presented group is equivalent either to a polynomial
or to the exponential function $2^n$?" The survey calls it "the main remaining open problem
concerning group growth" and states the stronger conjecture "A finitely presented group either
contains a free subsemigroup on two generators or is virtually nilpotent."

## Known obstructions (imported, secondary)

- Torsion spinal groups are not finitely presented (Bartholdi–Grigorchuk–Šunić, *Branch groups*,
  arXiv:math/0510294, Corollary `theorem:spinalnotfp`); their questions list asks "Do there exist
  finitely presented branch groups?"
- Any finitely presented group mapping onto the first Grigorchuk group contains a free subgroup
  on two generators, hence has exponential growth (de la Harpe and Grigorchuk, as stated in the
  survey; Benli–Grigorchuk–de la Harpe was not read here).

## Attempts

1. **Maps onto Z** (2026-09-13). `intermediate-growth-z-quotient-kernels-fg-intermediate`: every
   epimorphism from a finitely generated group of intermediate growth onto `Z` has a finitely
   generated kernel of intermediate growth. So a witness with positive virtual first Betti number
   is virtually `N ⋊ Z` with `N` finitely generated of intermediate growth. This does not use
   finite presentation.
2. **Ascending HNN envelopes** (2026-09-13). The finitely presented amenable envelopes built from
   Lysionok-type presentations are ascending HNN extensions along non-surjective endomorphisms.
   `ascending-hnn-non-surjective-contains-free-subsemigroup` shows every such extension of a
   finitely generated group contains a free subsemigroup of rank 2, so this construction always
   yields exponential growth.
3. **Truncated presentations** (2026-09-13). `fp-intermediate-growth-iff-subexponential-truncation`:
   a witness exists exactly when some finitely generated group `Q` of intermediate growth has a
   truncated presentation `P_n(Q)` (all relators of length `<= n`) of subexponential growth.
   Equivalently, a witness is a marked group with a neighbourhood of quotients, all of
   subexponential growth.
4. **Deficiency and mod-p homology** (2026-09-14).
   - `fp-subexponential-growth-forces-sqrt-mod-p-betti-bound`: a finite presentation `⟨X | R⟩` of a
     group of subexponential growth has `|X| − |R| ≤ 1`, by the Golod–Shafarevich test on covering
     presentations.
   - The same count bounds every finite-index `U` with `d_p(U) ≥ 2`:
     `(d_p(U) − 2)² ≤ 4[G:U](|R| − |X| + 1)`.
   - `intermediate-growth-groups-have-deficiency-at-most-zero`: deficiency one is impossible for
     intermediate growth. The presentation complex is aspherical by ℓ²-vanishing, and Kochloukova's
     Theorem 3 makes the finitely generated kernel of a map onto `Z` free.
   - A witness therefore has deficiency at most 0.
   - If an intermediate growth group has a finite 2-dimensional `K(G,1)` with `χ = 0`, then all its
     finite-index subgroups have finite abelianization.

## Exact gap

Exhibit a finitely generated group `Q` of intermediate growth and `n` such that the finitely
presented cover `P_n(Q)` contains no free subsemigroup-type growth, i.e. has subexponential
growth. For the first Grigorchuk group every finitely presented cover contains `F_2`.

Presentation side (2026-09-14): any witness `⟨X | R⟩` has `|R| ≥ |X|` and the square-root mod-`p`
Betti bound above. Deficiency 0 is where these tools stop.
- A balanced presentation complex has `χ = 1`, so it is never aspherical for an infinite amenable
  group.
- Kochloukova's Theorem 3 needs a finite `K(G,1)` with `χ = 0`.
- The Golod–Shafarevich bound `d_p(U) ≤ 2 + 2√[G:U]` does not bite on branch-type groups, where
  `d_p` of finite-index subgroups grows logarithmically in the index.
