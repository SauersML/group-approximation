---
rg: 2
id: abdollahi-taheri-pentagon-relations-73-and-77-are-trefoil-type
kind: claim
title: Two 5-cycle relations that Abdollahi--Taheri mark as contradictions define the trefoil group, not a solvable group
distinct_from:
  f2-support-three-zero-divisors-need-support-at-least-22: that bound excludes graphs by its own exhaustive search; this is a correction to one step of the forbidden-subgraph analysis in the paper it cites.
  kaplansky-graph-squares-force-central-trefoil-generators: that derives trefoil structure from 4-cycles; this finds the same structure in two 5-cycle relations that the source excludes by a faulty computation.
artifacts:
  - research/artifacts/zds-three-support-theory-2026-09-13.md
---

**ESTABLISHED.** In Abdollahi--Taheri, arXiv:1612.00934 (TeX source), the
appendix Table `tab-C5` lists 105 classes of 5-cycle relations in a Kaplansky
graph and stars 35 of them as contradictions. Two starred rows are not
contradictions:
- row `(73)`: `h_2h_3^{-2}h_2^2h_3^{-1}h_2=1`;
- row `(77)`: `(h_2h_3^{-2})^2h_2=1`.

The appendix argues (73) as "Using Tietze transformation where
`h_3\mapsto h_2h_3` and `h_2\mapsto h_2`, we have:
`h_2h_3^{-1}h_2^{-1}h_3^{-2}=1\Rightarrow h_2^{-1}h_3^{-2}h_2=h_3\Rightarrow \langle h_2,h_3\rangle\cong BS(-2,1)`
is solvable, a contradiction". It argues (77) "By interchanging `h_2` and
`h_3` in (73)".

**What is true.**
1. The substitution `h_3 -> h_2 h_3` sends relator (73) to
   `h_2 h_3^-1 h_2^-1 h_3^-1 h_2 h_3^-1`, not to the displayed word of length 5.
2. The automorphism `h_2 -> h_2`, `h_3 -> h_3 h_2^2` sends (73) to a cyclic
   conjugate of `h_3^-3 h_2^-2`. The automorphism `h_2 -> h_2 h_3^2`,
   `h_3 -> h_3` sends (77) to `h_2^3 h_3^2`. So each one-relator group
   `<h_2, h_3 | r>` is the trefoil group `<a, b | a^3 = b^2>`.
3. The trefoil group is torsion-free, non-abelian and not solvable. In it the
   images of `1`, `h_2` and `h_3` are pairwise distinct. So neither relation
   contradicts torsion-freeness, commutativity or elementary amenability on
   its own. Like the nine surviving 4-cycle classes, each forces a central
   element in `<h_2, h_3>`.
4. The other 33 starred rows are contradictions of the kinds the census
   recognizes: `H` cyclic in 15 classes, `H` solvable in 18. No unstarred row
   is one.

**Consequence.** Any forbidden subgraph in A--T §5 whose exclusion uses a
pentagon only through relation (73) or (77) is not established by the
argument as written. Which of the 44 subgraphs depend on these rows was not
checked here.

The bound `f2-support-three-zero-divisors-need-support-at-least-22` cites
A--T Cor 6.2 for `n >= 20` in step (2) of its route. The artifact
`zero-divisor-search-2026-09-12.md` §6 excludes every graph with at most 18
vertices by its own search, without forbidden subgraphs. So the lower bound
itself survives, but step (2) should cite that search instead of Cor 6.2.

DERIVATION
[[abdollahi-taheri-pentagon-73-77-trefoil-proof]]
