---
rg: 2
id: peelable-extreme-one-relator-groups-are-sofic
kind: claim
title: A Magnus rewriting with a peelable extreme letter makes a one-relator group sofic
distinct_from:
  triangular-conjugate-bs-chains-are-sofic: that treats relators c^(-1) x^l c = x^k whose conjugator is a conjugate of a later generator power; this treats arbitrary coefficient words, constrained only by the syllable structure of one extreme letter.
  single-block-conjugator-one-relator-groups-are-sofic: that is the relator family (a^l)^(a^w) = a^k with w = b^p a^s b^q; this is a syllable condition on the Magnus rewriting of an arbitrary relator, and it contains relators with overlap rank two and non-power coefficients.
  one-sided-conjugator-one-relator-groups-are-sofic: that concerns the conjugator family w = b^d V with one-sided support; this concerns any relator whose top or bottom Magnus letter forms at most two equal-magnitude syllables.
  magnus-staggered-chain-sofic: that asks for every staggered one-relator kernel; this proves the chains whose extreme letter can be peeled by cyclic amalgams and HNN extensions, and isolates the unpeelable remainder.
  residually-rationally-solvable-one-relator-sofic: that closes the trivial-Linton-radical class by residual properties; this closes a syllable class that includes non-residually-solvable examples such as the Baumslag--Gersten and Berlai groups.
  berlai-nonresidual-one-relator-families-sofic: that imports two explicit families; this is a general syllable criterion containing the first of them.
artifacts:
  - research/artifacts/peelable-extreme-one-relator-sofic-2026-09-11.md
---

ESTABLISHED (written proof; not Lean-checked). Let `G = <a,t | w>` with `w`
cyclically reduced and not a proper power, and assume `t` has exponent sum
zero in `w`. Rewrite a cyclic permutation of `w` as `W_0(a_m,...,a_n)` over
`a_i = t^(-i) a t^i`, with `m < n` the extreme indices.

Call the top letter `a_n` **peelable** when its occurrences in the cyclic word
`W_0` form one syllable, or two syllables `a_n^e` and `a_n^(+-e)` with the same
absolute exponent; define peelability of `a_m` in the same way.

**Theorem.** If the top or bottom letter of `W_0` is peelable, then `G` is
sofic.

The proof processes the staggered truncations of the Magnus kernel one
relator at a time. The window step `S_(j-1) *_(F_j) B_j` is an amalgam over a
free group of rank `n-m`, but a peelable extreme letter enters `B_j` only
through cyclic subgroups of `F_j`: one syllable is a root adjunction, and two
equal-magnitude syllables give a cyclic HNN extension or a square-root amalgam
followed by a root adjunction. So each step is at most two cyclic amalgams or
HNN extensions of the previous truncation. The Freiheitssatz keeps the next
top Magnus subgroup free. Amenable-edge permanence, directed colimits, and the
amenable quotient `G/K = Z` finish the proof.

The class contains every Baumslag--Solitar group, the Baumslag--Gersten group,
the Berlai families `<a,b | (a^l)^(a^(b^n)) = a^(l+1)>`, and relators with
overlap rank two and non-power coefficients such as
`a_2 [a_0,a_1] a_2^(-1) [a_1, a_0 a_1]`.
