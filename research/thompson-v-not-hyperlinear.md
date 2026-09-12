---
rg: 2
id: thompson-v-not-hyperlinear
kind: claim
title: Thompson's group V is not hyperlinear
distinct_from:
  thompson-v-one-word-strict-hs-ceiling: that is the quantitative one-word energy ceiling for a fixed finite presentation; this is the qualitative approximation property. The binary trace face makes them equivalent, but the ceiling is the form an estimate can target, while this is the form other groups and branches consume.
  thompson-v-not-lef: that excludes exact local embeddings into finite groups, a classical and established fact; this excludes approximate unitary models in normalized Hilbert--Schmidt norm, which is open.
  leavitt-hyperlinear-branch-implies-thompson-v-hyperlinear: that records what the hyperlinear branch of the Leavitt fork would cost; this is the opposite answer for V itself, which selects the stable branch.
artifacts:
  - research/artifacts/thompson-v-one-word-ce-frontier-2026-08-21.md
---

**OPEN.** Thompson's group `V = G_(2,1)` admits no injective homomorphism into
a tracial matrix ultraproduct `prod_omega (M_n, tr_n)`.

## Why this is the cheapest nonhyperlinearity test in the graph

`V` is finitely presented, infinite and simple, has no nontrivial
finite-dimensional unitary representation
(`thompson-v-has-no-nontrivial-fd-unitary-representation`), and its only
extreme characters are the trivial and regular ones
(`thompson-v-character-simplex`). Consequently one nontrivial homomorphism
into a matrix ultraproduct is already injective, and every nontrivial word
then has squared HS energy `2t` for one common `t>0`. The claim is therefore
equivalent to the single scalar estimate `thompson-v-one-word-strict-hs-ceiling`.

It also sits inside the Leavitt fork. `V` embeds in `R^x`, `R=L_(F_2)(1,2)`,
by cylinder swaps (`leavitt-cylinder-swaps-generate-thompson-in-el`), and
`R^x = GL_4(R) = EL_4(R) = Q` (`leavitt-gl-equals-el-and-perfect-unit-group`).
Hyperlinearity passes to subgroups, so this claim makes `Q` nonhyperlinear and
selects the stable branch of `leavitt-steinberg-hs-stability-fork`
(route `thompson-v-nonhyperlinearity-selects-stable-steinberg-branch`).
Conversely every construction on `leavitt-steinberg-hs-unstable` must make
`V` hyperlinear.

## What a proof cannot use

`V` has the Haagerup property (Farley, *Proper isometric actions of
Thompson's groups on Hilbert space*, IMRN 2003, no. 45, 2409--2414), which
passes to subgroups, while an infinite group with property (T) is never
a-T-menable. So `V` contains no infinite Kazhdan subgroup. Every nonsoficity
and non-MF mechanism recorded in this graph -- the OpenAI expander-matching
criterion, Kun--Thom Theorem A, and the normal-Kazhdan corona detector --
needs an infinite Kazhdan subgroup, and none of them has an instance inside
`V` or any subgroup of `V`. A proof of this claim needs a mechanism without
property (T). This is recorded here as a scope statement, not as a separate
theorem.

## Attempts

The live attacks all target the equivalent one-word ceiling, and each one
is recorded at `thompson-v-one-word-strict-hs-ceiling`.

- **Porting Fournier-Facio--Rangarajan to normalized HS.** It dies at the
  nonabelian normalized-HS tangent quotient
  (`normalized-hs-tangent-quotient-is-nonabelian`) and at the gap between
  uniform and pointwise defect.
- **Pure prefix copying.** The affine clone model refutes it.
- **Coherent alternating packets.** Open at the nonlinear synchronization step
  (`thompson-v-r5-coherent-alternating-packet`).
- **Carmichael families.** Open (`thompson-v-r5-coherent-carmichael-family`).
  The subquadratic-energy variant is refuted, and the common-pivot centralizer
  subroute is closed.
- **Kazhdan compression.** It has no instance inside `V`, as above.
