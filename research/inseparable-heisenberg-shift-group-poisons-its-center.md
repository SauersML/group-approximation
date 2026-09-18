---
rg: 2
id: inseparable-heisenberg-shift-group-poisons-its-center
kind: claim
title: For every cyclic order there is a three-generator computably presented group with a central element that survives only in quotients with unsolvable word problem
distinct_from:
  miller-amalgam-ck-envelopes-have-no-fng-maximal-kernel: that uses Miller's finitely presented group all of whose nontrivial quotients are undecidable, amalgamated into the envelope input; this is a computably presented group in which only quotients keeping one central element of prescribed order alive are undecidable, which lets the poisoned element be identified with a torsion normal generator.
  simple-envelope-forces-solvable-word-problem: that proves that finitely generated subgroups of finitely presented simple groups have solvable word problem; this builds a computably presented group whose every quotient that keeps one named element alive has unsolvable word problem, so it can never reach such an envelope.
  novikov-boone-fp-group-undecidable-word-problem: that exhibits one finitely presented group with unsolvable word problem; this makes unsolvability hereditary to every quotient in which a central element survives, and the device is a pair of recursively inseparable sets written into commutators, not a Turing machine simulation.
  poisoned-ck-envelopes-have-no-fng-maximal-kernel: that feeds this group, amalgamated with a simple core, to Chatterji--Kassabov and refutes the universal maximal-kernel claim; this is only the poisoned input group itself.
artifacts:
  - research/inseparable-heisenberg-shift-group-poisons-its-center-proof.md
---

**ESTABLISHED** (proof in [[inseparable-heisenberg-shift-group-poisons-its-center-proof]]).

Fix `k in {2, 3, 4, ...} ∪ {∞}` and disjoint recursively enumerable sets
`A, B ⊆ {1, 2, 3, ...}` that are recursively inseparable. Put

    Q_k = < a, b, c |  c^k,  [a,c],  [b,c],
                       [b, a^-n b a^n]        (n in A),
                       [b, a^-n b a^n] c^-1   (n in B) >

(omit `c^k` when `k = ∞`). Then:

1. `Q_k` is finitely generated and computably presented, and `c` has order exactly `k` in `Q_k`.
2. If `π : Q_k -> L` is any homomorphism with `π(c) != 1`, then `π(Q_k)` has unsolvable word
   problem. So every group containing such an image has unsolvable word problem.

In words: the central element `c` is *word-problem poisoned*. Any quotient that keeps it alive
must separate `A` from `B` through the commutators `[b, a^-n b a^n]`, and no algorithm can do
that.

This gives the key lemma behind C. F. Miller III's finitely presented group all of whose
nontrivial quotients have unsolvable word problem (*The word problem in quotients of a group*,
in Aspects of Effective Algebra, 1981, pp. 246--250). The proof here is self-contained and does
not rely on that source; the attribution is background only. Composed with
`chatterji-kassabov-normal-generator-embedding` it gives the finitely presented, property (T)
version in [[poisoned-ck-envelopes-have-no-fng-maximal-kernel]].
