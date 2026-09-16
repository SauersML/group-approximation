---
rg: 2
id: every-raag-in-2v-via-full-shift-full-group
kind: route
title: Right-angled Artin groups reach 2V through the topological full group of the full shift
target: every-raag-embeds-in-brin-thompson-group-2v
requires:
  - every-raag-embeds-in-full-shift-topological-full-group
  - full-shift-topological-full-group-embeds-in-2v
---

Compose the two embeddings. For a finite simple graph `Γ`,
`every-raag-embeds-in-full-shift-topological-full-group` gives an injective
homomorphism `A_Γ → [[{0,1}^Z]]`, and
`full-shift-topological-full-group-embeds-in-2v` gives an injective homomorphism
`[[{0,1}^Z]] → 2V`. The composite is an injective homomorphism `A_Γ → 2V`. A
finitely generated right-angled Artin group is `A_Γ` for a finite graph `Γ`,
since its abelianization is free abelian of rank `|V(Γ)|`. ∎
