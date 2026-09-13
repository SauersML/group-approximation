---
rg: 2
id: ershov-partial-torelli-subgroups-finitely-presented
kind: claim
title: "Partial Torelli subgroups of Aut(F_n) fixing the first d columns or rows of the abelianization are finitely presented for n >= d + 115"
---

Let `ρ: Aut(F_n) -> GL_n(Z)` be the action on `Z^n`. Let `Col_{n,d}` (resp.
`Row_{n,d}`) be the matrices whose first `d` columns (resp. rows) are those of the
identity, and `IAC_{n,d} = ρ^{-1}(Col_{n,d})`, `IAR_{n,d} = ρ^{-1}(Row_{n,d})`.
Then `IAC_{n,d}` and `IAR_{n,d}` are finitely presented for `n >= d + 115`, and for
`d = 1` they are finitely presented for all `n >= 26` (Ershov, arXiv:2601.01377,
Theorem 1.1). The import is `ershov-partial-torelli-subgroups-finitely-presented-citation`.

Role in Zaremsky Problem 3.1: `IA_n = IAC_{n,n}` is the endpoint `d = n`, outside
the theorem's range. The method is Brown's criterion through van Kampen diagrams
with peak reduction. It is the closest known finite presentability result to
`ia-automorphism-groups-fp-for-large-rank`.
