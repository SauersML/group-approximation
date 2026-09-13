---
rg: 2
id: ia-n-fp-iff-outer-torelli-fp
kind: claim
title: "For n >= 2, IA_n is finitely presented if and only if the Torelli group of Out(F_n) is"
---

For every `n >= 2`, the group `IA_n = ker(Aut(F_n) -> GL_n(Z))` is finitely
presented if and only if `T_n = ker(Out(F_n) -> GL_n(Z))` is finitely presented.

The proof is in `ia-n-fp-iff-outer-torelli-fp-proof`: `IA_n` is an extension of
`T_n` by `Inn(F_n) ≅ F_n`, and finite presentability passes both ways across an
extension with a finitely presented kernel.

Consequences: the Aut and Out families of Zaremsky Problem 3.1 have the same
answer, rank by rank. `IA_2 ≅ F_2` because `T_2` is trivial, and `IA_3` is not
finitely presented because `T_3` is not.
