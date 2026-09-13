---
rg: 2
id: kirby-freedman-one-factor-injects-when-a-is-torsion-free
kind: claim
title: If A is torsion-free and B is nontrivial, then A or B injects into A * B modulo any one relator
distinct_from:
  torsion-free-free-products-have-normal-rank-above-one: that is the normal-rank form with both factors torsion-free; this is the injectivity question as printed in Kirby's 1995 list, with only A torsion-free, and a positive answer implies that form.
  lo-syllable-relators-keep-free-factors: that proves both maps injective when the syllable subgroups of the relator are orderable; this asks for one injective map with no hypothesis on the relator.
  klyachko-kl-holds-for-torsion-free: that is the case B = Z with exponent sum ±1, where A injects; this asks it for every nontrivial B and every relator.
artifacts:
  - research/artifacts/solve-kirby-66-2026-09-13.md
---

**OPEN.** Source: R. Kirby, *Problems in low-dimensional topology* (1995 list,
`problems.ps.gz` from `math.berkeley.edu/~kirby`, text extracted on MSI),
Problem 5.7 (Freedman), lines 9000–9003 of the extracted text:

> "It seems rare that both natural maps A → A∗B/r and B → A∗B/r have nontrivial
> kernels. This happens if A = Z/2Z, B = Z/3Z and r = ab. Are there any other
> examples of a different flavor? Specifically if A is torsion-free and B
> nontrivial, is either A or B into A∗B/r always an injection?"

Chen–Lodha (arXiv:2510.26073 v2, `wiegold.tex` l.225) cite "[Kir78, Problem 66]
contributed by Freedman" for the torsion-free normal-rank question. The 1978 list
itself was not read here: the PDF on MSI (`~/wiegold-lane/kirby78.pdf`) has no
text layer, and ghostscript extraction returned 0 bytes. That the 1995 Problem 5.7
is the 1978 Problem 66 is therefore likely, not checked.

**Statement.** Let `A` be torsion-free and `B` nontrivial. For every
`r ∈ A * B`, at least one of `A -> (A * B)/<<r>>` and `B -> (A * B)/<<r>>` is
injective.

## Attempts

1. **Orderable syllables** (solve-kirby-66, 2026-09-13). If `r` is conjugate into
   a factor, the other factor injects (`(A * B)/<<a>> = (A/<<a>>) * B`). Otherwise
   write a cyclically reduced conjugate `a_1 b_1 ... a_n b_n`. If
   `<a_1,...,a_n>` and `<b_1,...,b_n>` are left-orderable, both maps are injective
   by `lo-syllable-relators-keep-free-factors`. So a counterexample needs a
   non-orderable syllable subgroup: on the `B` side any syllable of finite order
   suffices, and on the `A` side a torsion-free non-orderable subgroup of rank at
   least 2.
2. **Known cases, as recorded at source.**
   - `B = Z`, exponent sum ±1: `A` injects (Klyachko; 1995 list, update to
     Problem 5.7, and `klyachko-kl-holds-for-torsion-free`).
   - Locally indicable `A` and `B`: both inject when `r` is not conjugate into a
     factor (Brodskiĭ, Howie, Short, per Chen–Lodha l.224; not read).
3. **Why only one map is asked for.** The torsion example `Z/2 * Z/3`, `r = ab`,
   kills both. Kirby's question allows `B` to have torsion, and in that range the
   syllable test says nothing whenever the `B`-syllables have finite order.

**Exact gap.** The relators left open are those whose cyclically reduced form has
a non-orderable syllable subgroup. For the torsion-free normal-rank form this is
K1 of `normal-generators-of-free-products-have-non-lo-syllables`.
