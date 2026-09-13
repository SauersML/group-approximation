---
rg: 2
id: algebra-bh-via-simple-leavitt-nekrashevych-completions
kind: route
title: Envelope decidable algebras by psi-minimal aperiodic Leavitt--Nekrashevych completions
requires:
  - decidable-algebras-embed-in-simple-ln-completions
  - leavitt-nekrashevych-completion-embeds-and-is-fp
  - leavitt-nekrashevych-completion-simplicity-criterion
target: algebra-boone-higman-conjecture
---

Let `A` be finitely generated with solvable word problem. By
`decidable-algebras-embed-in-simple-ln-completions`, `A` embeds in `O_psi` for a
finitely presented `B` with an injective, psi-minimal, aperiodic recursion `psi`.

- By `leavitt-nekrashevych-completion-embeds-and-is-fp`, `O_psi` is finitely
  presented.
- By `leavitt-nekrashevych-completion-simplicity-criterion` (part 3), `O_psi` is
  simple.

So `O_psi` is a finitely presented simple algebra containing `A`.
