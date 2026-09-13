---
rg: 2
id: zaremsky-1-08-bnsr-invariants-of-graph-braid-groups
kind: claim
title: "Zaremsky Problem 1.8 resolved: compute the BNSR invariants of graph braid groups"
root: true
---

M. C. B. Zaremsky, *Some open problems* (version of July 12, 2026,
https://zaremsky.github.io/open_problems.pdf), Section 1, Problem 8,
verbatim: "Compute the BNSR-invariants of graph braid groups."

This claim is the question. It is established only through an answer route:

- **Computation**: `zaremsky-1-08-by-formula` requires
  `graph-braid-group-sigma-invariants-explicit-formula`.

Never write a `requires: []` route into this claim.

**Reading.** For a finite connected graph `Γ` and `n ≥ 1`, the graph braid
group `B_nΓ` is the fundamental group of the unordered configuration space
`UConf_nΓ` of `n` distinct points in `Γ`. Abrams' discretized configuration
space `UD_nΓ` is a compact nonpositively curved cube complex. When `Γ` is
sufficiently subdivided, it is a deformation retract of `UConf_nΓ` (Abrams,
PhD thesis, Berkeley 2000; the subdivision condition was improved by
Kim–Ko–Park, arXiv:0805.0082, and by Prue–Scrimshaw). So `B_nΓ` has a finite
`K(π,1)`: it is of type F, and every `Σ^m(B_nΓ)` is defined. The BNSR
invariants are the subsets `Σ^m(B_nΓ) ⊆ S(B_nΓ) = (Hom(B_nΓ,ℝ) \ 0)/ℝ_{>0}`
for `m ≥ 1`, together with `Σ^∞ = ⋂_m Σ^m`.

An answer states, for every finite connected graph `Γ` and every `n`, an
explicit criterion in terms of `Γ`, `n` and the character, with no
unevaluated topological input, deciding whether `[χ] ∈ Σ^m(B_nΓ)`. This is
the model of Meier–Meinert–VanWyk for right-angled Artin groups
(arXiv:math/9310202 for `Σ¹`). The character sphere itself needs `H_1(B_nΓ)`,
which Ko–Park compute (arXiv:1101.2648, *Discrete Comput. Geom.* 2012).

**Status (searched 2026-09-13, web search only).** No computation of
`Σ¹(B_nΓ)` for general graphs was found. Related computed invariants:
`Σ¹` of pure braid groups (Koban–McCammond–Meinert, arXiv:1306.4046); `Σ¹` of
surface braid groups for the sphere, projective plane, torus and Klein
bottle (arXiv:2308.12377). Structure theorems that constrain the answer:
hyperbolicity of `B_nΓ` (Genevois, arXiv:1912.10674), and when `B_nΓ` is a
RAAG (Kim–Ko–Park, arXiv:0805.0082).

## Attempts

- 2026-09-13 (lane z1-08-graph-braid): the plan is Bestvina–Brady Morse
  theory on the CAT(0) universal cover of `UD_nΓ`. First show that the
  characters are affine, i.e. constant on hyperplanes. Then describe the
  ascending links as flag complexes of particle moves, prove the sufficient
  criterion, and settle the converse family by family: trees, graphs whose
  braid groups are surface groups, and RAAG cases. Partial results land as
  separate claims routed toward
  `graph-braid-group-sigma-invariants-explicit-formula`.
