---
rg: 2
id: closed-mcg-finite-index-subgroups-do-not-embed-in-v
kind: claim
title: No finite-index subgroup of the mapping class group of a closed surface of genus at least two embeds in Thompson's group V
distinct_from:
  closed-surface-mapping-class-groups-satisfy-boone-higman: that asks for an embedding in some finitely presented simple group; this excludes the most familiar one, Thompson's group V, even for finite-index subgroups, because they contain Z² ∗ Z.
  thompson-v-finitely-presented-infinite-simple: that is finite presentability and simplicity of V; this is an obstruction to being a subgroup of V, imported from Bleak--Salazar-Díaz through the survey and combined with Koberda's theorem.
artifacts:
  - research/artifacts/bh-mcg-closed-surface-2026-09-12.md
---

**ESTABLISHED.** Let `Σ` be a closed orientable surface of genus `g ≥ 2`, and
let `L ≤ Mod(Σ)` have finite index. Then:
- `L` contains a subgroup isomorphic to `Z² ∗ Z`;
- `L` is not isomorphic to any subgroup of Thompson's group `V`;
- every homomorphism `L → V` has nontrivial kernel.

**Why it matters.** The finitely presented hosts of
`aramayona-funar-asymptotic-mcgs-are-fp-extensions-of-v` are extensions of `V`
(or of `V₂[Z₂] ≅ V`) by a compactly supported mapping class group. By this
claim, a copy of `L` inside one of them must meet the compactly supported
kernel nontrivially. It also excludes every quotient of such a host through
`V`. `closed-mcg-in-asymptotic-mcg-is-bordered-or-infinite-in-v` uses both.

**Scope.**
- **Subgroups only.** Infinite quotients of `L` inside `V` are not excluded.
- **Genus one is not covered.** The argument needs two disjoint, non-isotopic
  curves.
- **Other Higman--Thompson groups.** `V_{d,r}` for `(d, r) ≠ (2, 1)` is not
  addressed.

The derivation is `closed-mcg-v-nonembedding-via-koberda`.
