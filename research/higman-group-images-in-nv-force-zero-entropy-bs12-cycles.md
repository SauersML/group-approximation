---
rg: 2
id: higman-group-images-in-nv-force-zero-entropy-bs12-cycles
kind: claim
title: A nontrivial homomorphism from Higman's four-generator group to a Brin--Thompson group nV sends every generator to an infinite-order, zero-entropy element with an aperiodic core, and each consecutive pair generates BS(1,2)
distinct_from:
  higman-group-embeds-in-no-almost-automorphism-group: that kills every homomorphism into almost automorphism groups, including V_{d,r}; this gives necessary conditions on homomorphisms into nV, which that argument does not cover.
  higman-group-satisfies-boone-higman: that is the open embedding question; this restricts one untested host family.
  bs12-embeds-in-brin-thompson-2v: that asks whether nV contains one proper-power witness; this shows a copy of Higman's group in nV needs four of them in a cycle, each of zero entropy.
---

**ESTABLISHED** (elementary; no novelty claimed).

**Setting.**
- `H4 = < g_0, g_1, g_2, g_3 | g_i g_(i+1) g_i^-1 = g_(i+1)^2, i ∈ Z/4 >`.
- `ψ : H4 → nV` is a homomorphism, `n ≥ 1`, and `γ_i = ψ(g_i)`.
- `Per`, `K`, `δ` and `h` are as in
  `bs-kl-images-in-brin-thompson-groups-have-open-periodic-sets` and
  `brin-thompson-proper-power-conjugates-have-zero-entropy`.

**Statement.**
1. **Finite order kills the image.** If some `γ_i` has finite order, then `ψ` is
   trivial.
2. **Baumslag--Solitar pieces.** If `ψ` is nontrivial, every `γ_i` has infinite
   order. For each `i`, `u ↦ γ_i`, `s ↦ γ_(i+1)` is an isomorphism from
   `BS(1,2) = < u, s | u s u^-1 = s^2 >` onto `<γ_i, γ_(i+1)>`. In particular
   `BS(1,2)` embeds in `nV`.
3. **Periodic structure.** If `ψ` is nontrivial, each `γ_i`:
   - has zero periodic exponents and an open periodic set `Per(γ_i)`, on which
     some power is locally the identity;
   - has a nonempty closed aperiodic core `K(γ_i)`, invariant under both `γ_i`
     and `γ_(i-1)`;
   - satisfies `|δ_(γ_i^N)(x)|_∞ ≤ c (1 + log|N|)^2` for all `N ≠ 0` and all `x`.
4. **Zero entropy.** Every `γ_i` has topological entropy `0`. So every
   conjugator in the cycle is a zero-entropy element of `nV`, and no `γ_i` can be
   a baker map or any other element of positive entropy.

**Corollary.** If `BS(1,2)` does not embed in `nV`, every homomorphism
`H4 → nV` is trivial. A copy of `H4` in `nV` needs four infinite-order,
zero-entropy elements, each conjugate to its own square by the previous one.

**Scope.**
- The case `n = 1` is already covered by
  `higman-group-embeds-in-no-almost-automorphism-group`.
- For `n ≥ 2` this does not decide the question. It reduces a copy of `H4` in
  `nV` to a cyclic arrangement of zero-entropy witnesses for
  `bs12-embeds-in-brin-thompson-2v`. It also rules out, as generators, the
  baker-map conjugators of the recorded odometer realization.

The proof is `higman-group-nv-image-constraints-proof`.
