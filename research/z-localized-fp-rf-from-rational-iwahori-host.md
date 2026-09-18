---
rg: 2
id: z-localized-fp-rf-from-rational-iwahori-host
kind: route
title: A finitely presented self-similar overgroup of the rational Iwahori group contains Z_(p) and is residually finite
target: z-localized-embeds-in-fp-rf-group
requires:
  - rational-iwahori-group-lies-in-fp-self-similar-group
---

Let `p` and `Λ <= Aut(T_p)` be as in `rational-iwahori-group-lies-in-fp-self-similar-group`.
- `Λ` is finitely presented.
- `Λ` is residually finite, since it acts faithfully on the rooted tree `T_p`.
- `Λ` contains the rational Iwahori group `Γ_p`, and `Γ_p` contains the
  translations `u -> u + c`, `c in Z_(p)`, a copy of `Z_(p)`. This is stated in
  `rational-iwahori-group-lies-in-fp-self-similar-group` ("`Γ_p` contains the
  translations by `Z_(p)`") and is visible from the Iwahori description of
  `pgl2-q-in-rover-nekrashevych-group-of-rational-iwahori`, item 2: the matrices
  `[[1,c],[0,1]]` with `c in Z_(p)`.

So `Λ` witnesses the target with `l = p`. ∎
