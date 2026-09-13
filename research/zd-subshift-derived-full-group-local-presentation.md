---
rg: 2
id: zd-subshift-derived-full-group-local-presentation
kind: claim
title: Derived full groups of free minimal Z^d-subshifts are presented by bounded local relations among small 3-cycles on cylinders
distinct_from:
  labbe-shift-derived-full-group-is-finitely-presented: That asks for finitely many relations; this asks for a presentation over an infinite generating set by relations of bounded size, which holds in dimension one (Grigorchuk--Medynets) although finite presentation fails there.
  minimal-z2-subshift-derived-full-groups-are-fg-simple: That imports finite generation and simplicity; this asks for a presentation by bounded local relations.
artifacts:
  - research/artifacts/fp-simple-relation-climbing-2026-09-13.md
---

**OPEN.**

**Setting.** `X ⊆ A^(Z^d)` is a free minimal subshift and `G = D([[Z^d ~ X]])`.
- `R_1` is the Chornyi–Juschenko–Nekrashevych radius (arXiv:1602.04255, line 166).
- Fix an enumeration `z_1, z_2, ...` of `Z^d` listing each `ℓ_1` ball first, and put
  `S_m = {z_1, ..., z_m}`.
- `𝒥_m` is the set of 3-cycles `T_(pi,(g_1,g_2,g_3))` (ChJN notation) with `pi` legal on `S_m`
  and `g_1, g_2, g_3` distinct vectors of `ℓ_1` length at most 1. Put `𝒥 = ∪_(m >= |B(R_1)|) 𝒥_m`.
- A **`(k, ℓ)`-local relation** is a word of length at most `ℓ` in at most `k` distinct letters
  of `𝒥` that is trivial in `G`.

**Statement.** There are `k_0` and `ℓ_0` such that the natural map
`<𝒥 | all (k_0, ℓ_0)-local relations> -> G` is an isomorphism.

**Why it matters.** It is the first half of `labbe-fp-via-local-relation-climbing`. Given it,
finite presentation of `G` is equivalent to `labbe-full-group-local-relations-climb`: finitely
many local relations at bounded scale imply all local relations.

**Model test.**
- **Dimension one.** Grigorchuk–Medynets (arXiv:1508.04454, Theorem `TheoremIntroMain`, lines
  75–96) present `G_T'` by five families of relations. Four have at most two letters; the
  refinement relations (R4) can be reduced to one-letter refinements with at most `|A| + 1`
  letters. So the statement should hold for `d = 1` after Tietze moves, which we have not written
  out.
- **Scope.** The statement concerns only presentations; it says nothing about finiteness, which
  fails for `d = 1` by Matui.

## Attempts

- **The Grigorchuk–Medynets proof, transported.** Not done.
  - Mechanism (source lines 505–690):
    - Present the locally finite group of permutations inside Kakutani–Rokhlin towers based
      at `omega`. This uses Vershik–Vsemirov relations for `Alt(n)` and simplicity.
    - Use `G_T' = G'_(T,omega) G'_(T,omega')` for two orbits (Theorem
      `TheoremPermutationProduct`, line 304).
    - Rewrite any product of generators into the two factors using only refinement and
      commutation relations.
  - Where it stops for `d = 2`.
    - Towers become castles with Følner shapes, and seams become one-dimensional walls.
    - Two castles do not suffice: elements supported near a crossing of the two seam networks
      lie in neither factor.
    - Three castles whose seam networks have no common point should replace the product
      decomposition (dimension `d + 1` factors, in the spirit of dynamic asymptotic dimension).
      Neither that decomposition nor the three-factor rewriting has been proved.
- **Simplicity alone.** Not enough. The epimorphism from the locally presented group onto `G`
  is injective on each locally finite tower subgroup by simplicity. Injectivity on products
  still needs the decomposition above.
