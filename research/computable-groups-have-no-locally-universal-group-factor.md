---
rg: 2
id: computable-groups-have-no-locally-universal-group-factor
kind: claim
title: The group von Neumann algebra of a computable countable group is not locally universal (given Arulseelan--Manzoor)
distinct_from:
  locally-universal-group-factor-group-is-nonhyperlinear: that shows a locally universal L(U) forces U to be non-hyperlinear; this rules out every computable group, in particular every finitely generated group with solvable word problem, as such a U.
  some-countable-group-factor-is-locally-universal: that is the open existence question; this is a necessary condition on any witness.
---

**Statement.**  Let `U` be a countable group given by a computable enumeration
`g_0 = e, g_1, g_2, ...` in which multiplication, inversion and equality are
computable.  Examples: every finitely generated group with solvable word
problem, enumerated through words.  Then `L(U)` admits a computable
presentation in the sense of Arulseelan--Manzoor, so by
`locally-universal-tracial-vna-no-computable-presentation` it is not locally
universal.

**Consequence.**  Any countable group whose group factor is locally universal
is not computable; if it is finitely generated, it has unsolvable word problem.
The witness sought by `some-countable-group-factor-is-locally-universal` must
therefore be non-computable.

**Conditionality.**  Inherited from the imported theorem, which rests on the
announced `MIPco = coRE`.

**Proof.**  Route `computable-group-factor-presentation-proof`.
