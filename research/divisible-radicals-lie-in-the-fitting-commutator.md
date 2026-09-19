---
rg: 2
id: divisible-radicals-lie-in-the-fitting-commutator
kind: claim
title: In a finitely generated group, a divisible abelian torsion normal subgroup inside a nilpotent normal subgroup N with virtually polycyclic quotient lies in [N, N], so Prüfer radicals of soluble minimax groups are always reached through commutator pairings; corner realizability reduces to monolithic groups whose monolith lies in such a pairing image
distinct_from:
  s-unit-twisted-prufer-radicals-have-isolated-hosts: that builds isolated hosts for given twisted Prüfer corners; this proves that the radical of every finitely generated soluble minimax group sits in a commutator (corner) position, and reduces the remaining realizability question to monolithic inputs.
  twisted-prufer-corners-embed-in-isolated-cornulier-hosts: that states corner realizability as the open condition of its Theorem B; this proves its structural half.
---

**ESTABLISHED** (lane proof, bh-free-60, 2026-09-19; elementary; not reviewed). No priority is
claimed.

**Standard facts used, not re-read.**
- P. Hall (1954): the integral group ring of a virtually polycyclic group is Noetherian, and
  virtually polycyclic groups are finitely presented.
- Fitting: a product of two nilpotent normal subgroups is nilpotent.
- A soluble minimax group is nilpotent-by-(virtually abelian); see for example Lennox–Robinson,
  *The Theory of Infinite Soluble Groups*, Ch. 5, which was not accessible here.

## Statement

**Theorem 1 (corner lemma).** Let `G` be finitely generated, `N ◁ G` nilpotent with `G/N`
virtually polycyclic, and `D ◁ G` a divisible abelian torsion subgroup. Then `D ≤ [ND, ND]`.
In particular, if `D ≤ N`, then `D ≤ [N, N]`.
- Let `i >= 2` be maximal with `D ≤ γ_i(ND)`.
- Then the image of `D` in `γ_i/γ_(i+1)` is nonzero, divisible, and lies in the image of the
  `i`-fold commutator map `(ND)_ab^(⊗ i) → γ_i/γ_(i+1)`.

**Theorem 2 (monolithic reduction).** Let `G` be finitely generated soluble minimax, `D` the
divisible part of `τ(G)`, and `p` a prime. Then (b) implies (a).
- (a) Some homomorphism from `G` to an isolated group is injective on `D_p[p]`. This is corner
  realizability in the sense of Theorem B of
  `twisted-prufer-corners-embed-in-isolated-cornulier-hosts`.
- (b) For every minimal normal subgroup `M` of `G` contained in `D_p`, the quotient `G/K_M`
  embeds in an isolated group, where `K_M` is any normal subgroup maximal among those meeting
  `M` trivially.

Each `Ḡ = G/K_M` is finitely generated, soluble, minimax and **monolithic**. Its monolith `M̄`
is a finite elementary abelian `p`-group. Moreover:
- `M̄` lies in the divisible radical `D̄` of `Ḡ`;
- `τ(Ḡ)` is a `p`-group;
- `M̄` is central in every nilpotent normal subgroup;
- by Theorem 1, `M̄ ≤ D̄ ≤ [N̄, N̄]`, where `N̄` is the Fitting subgroup of `Ḡ`.

## Proof

**Theorem 1.**
- Replace `N` by `ND`. It is nilpotent by Fitting, normal, and `G/ND` is still virtually
  polycyclic. So assume `D ≤ N`, and put `Q = G/N`.
- `Q` is finitely presented and `G` is finitely generated, so `N` is the normal closure in `G`
  of finitely many elements. Hence `N_ab` is a finitely generated `Z[Q]`-module, with `Q`
  acting by conjugation.
- `Z[Q]` is Noetherian, so the torsion submodule `t(N_ab)` is finitely generated, say by
  `x_1, …, x_k` of orders `n_j`. Every element of `t(N_ab)` is a `Z[Q]`-combination of the
  `x_j`, so `t(N_ab)` has exponent dividing `lcm(n_j)`.
- The image of `D` in `N_ab` is divisible and lies in `t(N_ab)`. A divisible group of bounded
  exponent is trivial, so `D ≤ [N, N]`.
- The layer statement: `D ≤ γ_2(N)`, and `N` is nilpotent, so a maximal `i` exists. The
  commutator map from `N_ab^(⊗ i)` onto `γ_i/γ_(i+1)` is standard. `∎`

**Theorem 2.**
- **Existence of `K_M`.** Zorn's lemma: the set of normal subgroups meeting `M` trivially is
  nonempty and closed under unions of chains.
- **`Ḡ` is monolithic.** A nontrivial normal subgroup of `G/K_M` has preimage properly
  containing `K_M`. So by maximality it meets `M`, and it contains the image of `M` by
  minimality of `M`.
- **Properties of `Ḡ`.**
  - The `p'`-part of `τ(Ḡ)` is normal and meets `M̄` trivially, so it is trivial.
  - The image of `D_p` is divisible and contains `M̄`, so `M̄ ≤ D̄`.
  - For a nilpotent normal `N`, `[M̄, N]` is normal and properly contained in `M̄` (nilpotency),
    so `[M̄, N] = 1` by minimality.
  - `Ḡ` is nilpotent-by-(virtually abelian), so Theorem 1 applies.
- **(b) ⇒ (a).** Let `Φ` be the finite union of the minimal normal subgroups of `G` inside
  `D_p` (see `isolated-embedding-of-soluble-minimax-groups-via-max-n-hosts`, item 1).
  - The product of the maps `G → G/K_M → I_M` is injective on each `M`.
  - Its kernel `J` is normal. If `J ∩ D_p[p] ≠ 1`, then `J ∩ D_p` is a nontrivial normal
    subgroup of `G`, so it contains some minimal normal `M ≤ D_p`, a contradiction.
`∎`

The converse, from (a) to (b), would need monolithic quotients of subgroups of isolated groups
to embed in isolated groups. That is not proved here.

## What remains for corner realizability (OPEN)

By Theorems 1 and 2 it suffices to embed in an isolated group every finitely generated,
soluble, minimax, monolithic `Ḡ` whose monolith `M̄` lies in `D̄ ≤ [N̄, N̄]`.

**Class 2.** When `N̄` has class 2, `D̄` lies in the image of the pairing
`N̄_ab ⊗ N̄_ab → N̄'`. That is exactly the Heisenberg corner of Cornulier's block group used by
`s-unit-twisted-prufer-radicals-have-isolated-hosts`. What is missing is an equivariant
embedding of an arbitrary such pairing, with the `Ḡ/N̄`-action, into a compactly presented
block group.

**Higher class.** Block unitriangular groups with blocks `(r, 3, …, 3, 1)` and `SL_3` Levi
factors contain `U_n` via `x ↦ x ⊗ E_11`. Their compact presentability at every prime (Abels'
`H_2` condition) is known here only for four blocks (Cornulier).

## Lesson for general BH

**Invisible torsion is always a corner.**
- In a finitely generated group whose Fitting quotient is virtually polycyclic, the
  abelianization of the Fitting subgroup is a Noetherian module, so its torsion has bounded
  exponent.
- Hence every Prüfer radical sits in commutators of the Fitting subgroup, never at the top.
- So the non-residually-finite part of a soluble minimax group is always created by a
  multilinear commutator pairing, as in Hall's example: there is no other way for it to arise.
- Isolated hosts therefore need only carry pairings, the Heisenberg or block-unitriangular
  corners, and compact presentability of those block groups is the one remaining arithmetic
  input.
