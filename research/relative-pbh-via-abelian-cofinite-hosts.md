---
rg: 2
id: relative-pbh-via-abelian-cofinite-hosts
kind: route
title: Embed the input in an abelian-cofinite host and glue a Houghton port along the abelian subgroup
target: relative-permutational-boone-higman-conjecture
requires:
  - decidable-groups-embed-in-abelian-cofinite-hosts
  - cofinite-abelian-subgroups-give-relative-pbh
---

Let `Γ` be finitely generated with solvable word problem.

1. **Host.** By `decidable-groups-embed-in-abelian-cofinite-hosts` (OPEN), `Γ ≤ D`, where
   `D` is finitely presented and acts faithfully on `X` with finitely generated stabilizers,
   and `A ≅ Z^n ≤ D` has finitely many orbits on `X`.
2. **Port.** By `cofinite-abelian-subgroups-give-relative-pbh`, with `Γ_H` its Houghton
   block group, `P = Γ_H *_A D` acts on `X × [2^n]` with type [A_2], and `D` meets its kernel
   trivially.
3. **Conclusion.** So `Γ ≤ D` sharply embeds in `(P, ker)`. ∎

**The remaining gate** is step 1. Its necessary conditions are recorded in the claim:
- solvable word problem;
- finitely many ends for each orbit's Schreier graph.
