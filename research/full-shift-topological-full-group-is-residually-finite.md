---
rg: 2
id: full-shift-topological-full-group-is-residually-finite
kind: claim
title: The topological full group of the two-sided full shift is residually finite, so none of its subgroups is an infinite finitely generated group of finite exponent
distinct_from:
  brin-thompson-2v-is-torsion-locally-finite: that is the open question whether every finitely generated periodic subgroup of 2V is finite, with the copy of [[σ]] inside 2V as a candidate source of counterexamples; this proves every subgroup of [[σ]] is residually finite, so that copy can refute it only with unbounded exponent.
  almost-automorphism-torsion-subgroups-are-rf: that proves residual finiteness of finitely generated torsion subgroups of one-dimensional almost automorphism groups by a pumping argument; this proves residual finiteness of the whole topological full group of the two-sided full shift, through its dense set of finite shift orbits.
  full-shift-topological-full-groups-are-torsion-locally-finite: that proves every finitely generated periodic subgroup of [[σ]] is finite, which is stronger; this is the elementary residual-finiteness statement it strengthens.
  fp-simple-groups-can-contain-infinite-finite-exponent-groups: that is the open existence question for finitely presented simple hosts of infinite bounded-exponent groups; this removes the copy of [[σ]] inside 2V as a bounded-exponent witness and says what a witness inside 2V must use instead.
---

**ESTABLISHED** by `full-shift-topological-full-group-is-residually-finite-proof` (lane proof,
bh-free-13, elementary; not independently reviewed). No priority is claimed; the statement is
folklore-level. The corollary uses Zelmanov's theorem (`restricted-burnside-finiteness`, cited).

## Statement

Let `A` be a finite alphabet with `|A| >= 2`, let `X = A^Z` with the left shift `σ`, and let `[[σ]]`
be the topological full group: the homeomorphisms `g` of `X` for which some continuous
`k_g : X -> Z` satisfies `g(x) = σ^(k_g(x))(x)` for all `x`.

1. The restriction map `ρ : [[σ]] -> ∏_O Sym(O)`, over all finite `σ`-orbits `O ⊂ X`, is an injective
   homomorphism. So `[[σ]]` embeds in a direct product of finite groups, and is residually finite.
2. Every finitely generated subgroup of `[[σ]]` of finite exponent is finite.
3. **Consequence for `2V`.** Identify `{0,1}^N × {0,1}^N` with `{0,1}^Z`; the baker map is then `σ`,
   and `[[σ]] ≤ 2V` (Salo, arXiv:2103.06663, abstract; also the lane remark in
   `brin-thompson-2v-is-torsion-locally-finite`). By item 2, no infinite finitely generated
   bounded-exponent subgroup of `2V` lies in a conjugate of this copy of `[[σ]]`. A bounded-exponent
   witness for `fp-simple-groups-can-contain-infinite-finite-exponent-groups` inside `2V` must use
   elements that do not preserve the set of `σ`-periodic configurations, i.e. elements that rewrite a
   window or change window lengths. The copy of `[[σ]]` can still refute
   `brin-thompson-2v-is-torsion-locally-finite` with unbounded exponent (for example by an embedded
   Grigorchuk-type group), since periodic residually finite groups can be infinite.

## Scope

- The proof uses only that `g` preserves every `σ`-orbit and that periodic points are dense. So the
  same conclusion holds for the topological full group of any subshift with a dense set of periodic
  points (every irreducible shift of finite type, every irreducible sofic shift), and for every
  group of homeomorphisms of a compact space that preserves each orbit of a dense family of finite
  sets.
- **Superseded in strength.** `full-shift-topological-full-groups-are-torsion-locally-finite` (bh-free-06, 360ac2690) proves every finitely generated periodic subgroup of `[[σ]]` is finite, which contains item 2 without Zelmanov. This node stays as the elementary residual-finiteness statement.
