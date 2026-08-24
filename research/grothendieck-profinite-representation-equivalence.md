---
rg: 2
id: grothendieck-profinite-representation-equivalence
kind: claim
title: Profinite isomorphism is equivalent to equivalence of linear representation categories
artifacts:
  - research/artifacts/invisible-quotients-architecture-audit-2026-08-23.md
---

Two imported statements.

1. **Grothendieck (1970).**  For a homomorphism `u: G_1 -> G_2` of finitely
   generated groups, the induced map on profinite completions
   `u^: G_1^ -> G_2^` is an isomorphism if and only if, for every nonzero
   commutative ring `A`, restriction along `u`

   ```text
   u_A* : Rep_A(G_2) -> Rep_A(G_1)
   ```

   is an equivalence of categories, where `Rep_A` is the category of finitely
   presented `A`-modules with a group action.  So "same finite quotients,
   functorially" is the same condition as "same finitely presented linear
   representation theory over every ring".

2. **Bridson--Grunewald (2004).**  There are finitely presented residually
   finite groups `P < Gamma` of infinite index with `P` not isomorphic to
   `Gamma` and `P^ -> Gamma^` an isomorphism.  Such a pair is called a
   Grothendieck pair, and their existence answers Grothendieck's 1970 question
   negatively.

Sources: A. Grothendieck, *Representations lineaires et compactification
profinie des groupes discrets*, Manuscripta Math. 2 (1970); M. Bridson and
F. Grunewald, *Grothendieck's problems concerning profinite completions and
representations of groups*, Ann. of Math. 160 (2004) 359--373.

Recorded scope note.  A further claim circulating in the program's planning
material -- that Jaikin-Zapirain and Lubotzky, *Some remarks on Grothendieck
pairs*, Groups Geom. Dyn. 19 (2025), show Grothendieck pairs preserve Bohr or
proalgebraic completion data -- was **not** confirmed.  The article exists with
that title and those authors, but its abstract speaks of profinite rigidity and
left/right Grothendieck rigidity and says nothing about Bohr or proalgebraic
completions.  Nothing here or downstream uses such a statement.
