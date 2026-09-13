---
rg: 2
id: ia-automorphism-groups-fp-for-large-rank
kind: claim
title: "There is n_0 such that the IA-automorphism group IA_n of F_n is finitely presented for every n >= n_0"
---

Let `IA_n = ker(Aut(F_n) -> GL_n(Z))`. The claim: there is `n_0` such that `IA_n`
is finitely presented for every `n >= n_0`. It is the yes-answer for the Aut family
of Zaremsky Problem 3.1 (`zaremsky-3-01-aut-torelli-resolved`). By
`ia-n-fp-iff-outer-torelli-fp` it is equivalent to
`outer-torelli-groups-fp-for-large-rank`.

Known: `IA_n` is finitely generated (Magnus); `IA_2 ≅ F_2`; `IA_3` is not
finitely presented. Ershov (arXiv:2601.01377, abstract): "It is a long-standing
open problem whether the subgroup of IA-automorphisms `IA_n` is finitely presented
for `n >= 4`."

## Attempts

- **Partial Torelli overgroups** (Ershov, arXiv:2601.01377, Theorem 1.1).
  `IAC_{n,d}` and `IAR_{n,d}` are finitely presented for `n >= d + 115`, and for
  `d = 1` when `n >= 26`. The proof applies Brown's criterion through van Kampen
  diagrams with peak reduction over a super-Artinian order on cosets.
  `IA_n = IAC_{n,n}` is the unreached endpoint. Where it dies: the range condition
  `n >= d + 115`.
- **Passing to IA_n from an overgroup with abelian quotient.**
  `IA_n` is normal in `IAC^+_{n,n-1}` (first `n-1` columns of the identity,
  determinant 1), with quotient `Z^{n-1}`. If that overgroup were finitely
  presented, Renz's homotopical Σ-criterion would reduce finite presentability of
  `IA_n` to the characters vanishing on `IA_n` lying in `Σ²(IAC^+_{n,n-1})`. Where
  it dies: `d = n - 1` is outside Ershov's range, and the resulting condition is
  equivalent to the target rather than a genuine reduction. It is recorded here
  only as a map of where the difficulty sits.
- **Degree 2 homology.** Day–Putman (Geom. Topol. 21 (2017)) give a finite
  generating set for `H_2(IA_n)` as a `GL_n(Z)`-module. Finite generation as an
  abelian group is not known. Necessary, not sufficient.
