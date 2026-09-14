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

## Exact gap

Exhibit a finitely generated group `Q` of intermediate growth and `n` such that the finitely
presented cover `P_n(Q)` contains no free subsemigroup-type growth, i.e. has subexponential
growth. For the first Grigorchuk group every finitely presented cover contains `F_2`.
