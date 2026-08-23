---
rg: 2
id: single-finitely-presented-mf-radical-computer
kind: claim
title: One fixed finitely presented group has an undecidable promised word problem entirely inside its MF radical
artifacts:
  - GroupApproximation/Computability/MFRadicalComputer.lean
  - GroupApproximation/Endpoint/ChosenNonMFAudit.lean
distinct_from:
  threshold-free-mf-compiler-equivalence: that classifies moving-presentation compiler semantics; this fixes one finite presentation and encodes computation in a family of radical-valued words.
  novikov-boone-fp-group-undecidable-word-problem: that gives an undecidable word problem with no approximation promise; here every hard input is already proved invisible to all norm-matrix ultraproduct representations.
  authenticated-opnorm-challenge-compiler: that is a machine-indexed presentation compiler; this is a fixed-carrier exact algebraic computer.
---

There is one fixed finitely presented group `U_MF`, one fixed modular machine
with undecidable configuration halting, and a computable family of elements
`r_p in U_MF` such that

```text
r_p in Res_MF(U_MF)                 for every p,
r_p = 1  iff  the machine halts from p.
```

Consequently identity is undecidable even under the promise that the input
belongs to the MF radical.  Every `r_p` lies in
`[Res_MF(U_MF), U_MF]`, so the hard family is not a central or abelian
artifact.  The carrier is non-MF because it contains the literal non-MF group
as a free factor.

The Lean construction chooses the fixed controller from the repository's
closed modular-machine theorem, uses the already formalized explicit Boone
word, and gates it with the literal MF-invisible mark.  The closed endpoint is
`MFRadicalComputer.closed_package`; its theorem statement has no caller input,
literature premise, or conditional construction datum.
