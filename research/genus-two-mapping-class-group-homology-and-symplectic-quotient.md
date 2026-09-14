---
rg: 2
id: genus-two-mapping-class-group-homology-and-symplectic-quotient
kind: claim
title: The genus-two mapping class group is finitely presented, has H_1 = Z/10 and H_2 = Z/2, and maps onto Sp_4(Z) with kernel the Torelli group
distinct_from:
  genus-two-torelli-group-infinitely-generated: that imports the structure of the genus-two Torelli group (free, not finitely generated); this imports the low-degree integral homology of Mod(S_2) and the symplectic short exact sequence it sits in.
---

**ESTABLISHED by citation** (`genus-two-mapping-class-group-homology-citation`).

Let `Mod(S_2)` be the group of isotopy classes of orientation-preserving diffeomorphisms of the closed
oriented surface of genus two. Then:

1. `Mod(S_2)` is finitely presented.
2. `H_1(Mod(S_2); Z) ~= Z/10`.
3. `H_2(Mod(S_2); Z) ~= Z/2`.
4. The action on (co)homology gives a short exact sequence
   `1 -> I_2 -> Mod(S_2) -> Sp_4(Z) -> 1`, where `I_2` is the Torelli group.

**Trust surface.**
- Items 1–3 are quoted from a survey (Korkmaz), not from the primary sources (Wajnryb, Mumford,
  Benson–Cohen).
- Item 4 is quoted from Wikipedia wikitext. The Torelli kernel definition is cross-checked in
  Brendle–Margalit–Putman, arXiv:1211.4018v4, p. 1.
- The action on `H^1` and the action on `H_1` differ by `A -> (A^T)^(-1)`. On `Sp_4(Z)` this is
  conjugation by the standard symplectic form, so image and kernel are the same.
