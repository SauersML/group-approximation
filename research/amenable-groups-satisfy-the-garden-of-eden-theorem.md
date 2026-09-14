---
rg: 2
id: amenable-groups-satisfy-the-garden-of-eden-theorem
kind: claim
title: Over an amenable group a cellular automaton is surjective exactly when it is pre-injective
distinct_from:
  split-decoders-have-generic-cantor-fibers: that proves, over every group, that a decoder with a cellular section is pre-injective only when bijective; this is the classical Moore--Myhill equivalence of surjectivity and pre-injectivity, which needs amenability.
  sofic-groups-are-surjunctive: that is Gromov--Weiss surjunctivity for sofic groups; this is the Garden of Eden theorem for amenable groups, a two-sided equivalence about pre-injectivity.
artifacts:
  - research/artifacts/table-group-holonomy-normal-form-2026-09-12.md
---

**ESTABLISHED** by citation, `amenable-garden-of-eden-theorem-citation`.

Let `H` be an amenable group and `A` a finite alphabet. A cellular automaton
`A^H -> A^H` is surjective if and only if it is pre-injective, meaning that it
never maps two distinct configurations differing at finitely many sites to the
same configuration.

This is the Garden of Eden theorem:
- Moore and Myhill for `Z^d`;
- Machì and Mignosi for finitely generated groups of subexponential growth;
- Ceccherini-Silberstein, Machì and Scarabotti, *Amenable groups and cellular
  automata*, Ann. Inst. Fourier 49 (1999) 673--685, for all amenable groups.

It is also the main theorem of Chapter 5 of Ceccherini-Silberstein and Coornaert,
*Cellular Automata and Groups* (Springer, 2010). Bartholdi showed that the
implication "surjective implies pre-injective" characterizes amenable groups.

Only the forward implication, surjective implies pre-injective over amenable `H`,
is consumed here, by `amenable-decoder-memory-forces-surjectivity`.
