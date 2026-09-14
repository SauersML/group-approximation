---
rg: 2
id: bounded-generation-makes-el3-bi-interpretable-with-ring
kind: claim
title: For a finitely generated ring whose only central unit is 1, the ring is interpretable in EL_3 of it with parameters, and the two are bi-interpretable as soon as EL_3 is boundedly elementarily generated
distinct_from:
  subshift-el-group-interprets-its-crossed-product-ring: that is this statement's first half at the subshift crossed product, where the hypothesis on central units is the computation Z(R) = F_2.
  subshift-el-group-bi-interpretable-with-its-ring: that is this statement's second half at the subshift crossed product, where the bounded generation hypothesis is supplied by the 78-element bound.
artifacts:
  - research/artifacts/sk-first-order-plan-2026-09-14.md
---

**Statement.** Let `R` be a unital ring generated as a unital ring by a finite set `S ∋ 1`, and suppose the only central unit of `R` is `1`. Put `G = E_3(R)`. Then:

1. Each root subgroup is a centraliser of an explicit finite set,

       U_13 = C_G({e_12(s) : s ∈ S} ∪ {e_23(s) : s ∈ S}),

   and likewise after permuting coordinates. So `R` is interpretable in `G` with parameters: the domain is `U_13` with `e_13(r) ↔ r`, addition is the group law, and multiplication is `[w_{12}aw_{12}^{-1}, w_{23}bw_{23}^{-1}]` for Weyl parameters `w_{ij} ∈ G`.
2. If in addition there are `m` and fixed positions `(i_k,j_k)` with `G = e_{i_1j_1}(R) ⋯ e_{i_mj_m}(R)`, then `G` and `R` are bi-interpretable with parameters.

**Why the hypotheses are the right ones.**
- "Only central unit is `1`" is exactly what the centraliser computation needs: commuting with the two neighbouring root subgroups forces `g = cI + g_{13}E_{13}` with `c` a central unit.
- Bounded generation with a **fixed** position pattern is exactly what makes `G` existentially definable in `R`, and what gives the map `g ↦` its matrix a fixed arity. Without a bound, `E_3(R)` is an increasing union of sets of `n`-fold products and is not first-order in `R`.

**Instances.** For an infinite minimal subshift, `Z(R_X) = F_2` gives hypothesis 1 and the 78-element bound gives hypothesis 2, which is how `subshift-el-group-interprets-its-crossed-product-ring` and `subshift-el-group-bi-interpretable-with-its-ring` arise. The statement is stated in this generality so that it applies verbatim to any other elementary group in the programme once a bound is proved for it, for instance to the lamplighter hosts, where none is known.

**Credit.** Recovering a ring from a Chevalley-type group by centralisers of root subgroups, and using bounded elementary generation to make the group definable in the ring, is the standard route; it is the pattern used for `SL_n(O)` by Avni, Lubotzky and Meiri. What is contributed here is the packaging and the check that these hypotheses suffice. Bound of the novelty check: a grep of main only, no literature search.

**Status: established** by `bounded-generation-makes-el3-bi-interpretable-with-ring-proof`. UNREVIEWED; queued in the wave-12 verifier queue.

## Review
- **sk-verify-18 PASS-WITH-FIXES (2026-09-14, `research/artifacts/sk-verify-18-2026-09-14-part10.md`):** items 1–2 run verbatim with "c a central unit, so c = 1". Fix W1: outside characteristic 2 the Weyl parameters are signed permutations, so w_{ij}e_13(r)w_{ij}⁻¹ = e_ij(±r) and the commutator gives e_13(εrs) with a fixed sign ε; multiplication stays definable. Model test R = F_3, central unit 2, shows the hypothesis is needed.
