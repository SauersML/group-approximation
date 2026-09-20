---
rg: 2
id: brin-thompson-2v-not-a-t-menable-via-char-p-lamp-lifts
kind: route
title: "2V is not Haagerup if 2V lifts, through one affinely spanning phi : C^2 -> (F_p^2)^Z, affine maps whose linear parts generate EL_2(F_p[t,t^-1]); Theorem R with n = 2 does the rest"
target: brin-thompson-2v-is-not-a-t-menable
requires:
  - char-p-burger-lamp-realizations-refute-haagerup
  - brin-thompson-2v-lifts-el2-laurent-linear-ca-generators
---

Apply Theorem R of `char-p-burger-lamp-realizations-refute-haagerup` with `n = 2`. Its hypotheses
are exactly the conclusion of `brin-thompson-2v-lifts-el2-laurent-linear-ca-generators`:
- a continuous affinely spanning `φ : C^2 → (F_p^2)^Z`;
- `g_1, ..., g_k ∈ 2V` with `φ∘g_i = a_i∘φ`;
- `⟨γ_i⟩ ⊇ EL_2(F_p[t,t^-1])`.

Theorem R then gives a subgroup `G = M' ⋊ Λ ≤ 2V` with `M'` infinite and `(G, M')` of relative
property (T). Relative (T) with an infinite `M'` is incompatible with the Haagerup property, since
the Haagerup property passes to subgroups and a Haagerup group has relative (T) only with respect
to finite subsets (Bekka–de la Harpe–Valette, Chapter 2). Theorem R states this conclusion
directly. So `2V` is not Haagerup. ∎

**Status of the inputs.**
- The first input is ESTABLISHED.
- The second is OPEN. Its Attempts record the class kills:
  - baker lifts (w21);
  - piecewise-baker lifts, giving monomial linear parts
    (`piecewise-baker-torus-lifts-force-monomial-lamp-linear-parts`);
  - injective realizations for `p ≥ 3`.

This makes the second input the last missing hole of this route.
