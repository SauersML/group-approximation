---
rg: 2
id: ia-automorphism-groups-not-fp-for-infinitely-many-ranks
kind: claim
title: "For infinitely many n the IA-automorphism group IA_n of F_n is not finitely presented"
---

Let `IA_n = ker(Aut(F_n) -> GL_n(Z))`. The claim: `IA_n` is not finitely presented
for infinitely many `n`. It is the no-answer for the Aut family of Zaremsky
Problem 3.1 (`zaremsky-3-01-aut-torelli-resolved`), and the negation of
`ia-automorphism-groups-fp-for-large-rank`. By `ia-n-fp-iff-outer-torelli-fp` it is
equivalent to `outer-torelli-groups-not-fp-for-infinitely-many-ranks`.

The only rank known to fail is `n = 3`.

## Attempts

- **Transfer from the Out family.** Any rank where `T_n` is not finitely presented
  is a rank where `IA_n` is not (`ia-n-fp-iff-outer-torelli-fp`), and conversely.
  The attacks live on `outer-torelli-groups-not-fp-for-infinitely-many-ranks`.
- **Johnson-homomorphism quotients.** `IA_n` surjects onto `Hom(Z^n, Λ²Z^n)` via
  the first Johnson homomorphism. The successive quotients of the Johnson filtration
  embed in the finitely generated abelian groups `Hom(Z^n, L_{k+1}(Z^n))`, and the
  terms of the filtration are finitely generated in a linear stable range
  (Church–Ershov–Putman, arXiv:1711.04779). Such quotients are finitely presented,
  so they do not obstruct finite presentability. Where it dies: no quotient or
  subquotient that is not finitely presented is known.
