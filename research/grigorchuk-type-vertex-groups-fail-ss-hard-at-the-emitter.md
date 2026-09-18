---
rg: 2
id: grigorchuk-type-vertex-groups-fail-ss-hard-at-the-emitter
kind: claim
title: Grigorchuk and Šunić groups fail (SS-hard)_1. No branch group is known to be finitely presented (the first Grigorchuk group provably is not); hardness in the Grigorchuk family needs infinitely many self-similarity types; and Grigorchuk's finitely presented envelope is an ascending HNN extension over an infinite-index subgroup, i.e. an infinite emitter
requires:
  - faithful-finite-index-hnn-upgrades-to-half-tree-free
  - grigorchuk-ascending-hnn-extension-is-finitely-presented
  - grigorchuk-group-is-just-infinite-torsion-not-fp
  - rational-homeomorphism-subgroups-have-exponential-wp
distinct_from:
  kms-metabelian-layer-commensurations-have-finite-order: that closes the solvable (KMS) candidates for (SS-hard)_1 up to a division shape; this tests the branch-type candidates named there and finds the finite-presentation wall.
  computable-grigorchuk-groups-satisfy-boone-higman: that asks for fp simple hosts of computable G_ω; this records why those G_ω cannot be the vertex group of a finite-type E3′ host, and that their finitely presented envelope sits at an emitter.
  fp-group-of-intermediate-growth-exists: that asks for an fp group of intermediate growth; this uses only the related fact that no finitely presented branch group is known.
---

**ESTABLISHED** for items 2 and 4 (lane proof, bh-e3prime, 2026-09-18; elementary; not
reviewed). Items 1 and 3 import or recall stated results; each import is marked. (SS-hard)_1 stays
**OPEN**.

## Statement

1. **The Noetherian candidate is probably bounded (quick check, not settled).**
   - Metabelian groups have uniformly polynomial word problems: by Remeslennikov and Wehrfritz,
     finitely generated metabelian groups are linear over finite products of fields (recalled), and
     linear groups are easy.
   - For abelian-by-polycyclic groups the word problem reduces to membership in a fixed submodule of
     a finitely generated module over the Noetherian ring `Z[P]` (P polycyclic, Hall). A word of
     length `ℓ` gives an element whose support has `2^(O(ℓ))` monomials.
   - Reduction by a fixed Gröbner-type basis should then take time `2^(2^(O(ℓ)))`, uniformly over the
     class. This is a lane sketch only.
   - If it holds, the class shares one recursive bound and cannot supply (SS-hard)_1. The lane
     therefore moved to branch-type groups, as planned.
2. **Grigorchuk's envelope is an emitter.** Let `G = ⟨a, c, d⟩` be the first Grigorchuk group, and
   `φ(a) = aca`, `φ(c) = cd`, `φ(d) = c` Lysionok's substitution. Then:
   - `ψ(φ(g)) = (θ(g), g)` for the homomorphism `θ : G -> ⟨a, d⟩ ≅ D_8` with `θ(a) = d`,
     `θ(c) = θ(d) = a`;
   - so `[G : φ(G)] = ∞`.

   So Grigorchuk's finitely presented group `G*_φ` is an ascending HNN extension over an
   infinite-index edge group. Every vertex of its Bass–Serre tree has infinitely many edges, and `G`
   acts on the infinite coset set `G/φ(G)`. The vertex group sits at an infinite emitter: this is
   gate (IE), not the finite-type regime.
3. **Branch groups fail the finite-presentation requirement.**
   - (SS-hard)_1 needs a vertex group of type `F_2`.
   - The first Grigorchuk group is not finitely presented (`grigorchuk-group-is-just-infinite-torsion-not-fp`).
   - Contracting regular branch groups are not finitely presented (Bartholdi, recorded on main).
   - "Do there exist finitely presented branch groups?" is an open printed question (recorded in
     `fp-group-of-intermediate-growth-exists` and its pins).
   - So no branch group is currently available as a vertex group.
4. **Hardness in the Grigorchuk family needs infinitely many types.**
   - `G_ω` has solvable word problem iff `ω` is computable (Grigorchuk 1984, recalled).
   - Its natural section structure has state groups `G_(σ^n ω)`. These form a finite family iff `ω`
     is eventually periodic.
   - In that case the generated self-similar group is contracting
     (`eventually-periodic-grigorchuk-groups-satisfy-boone-higman`), so its word problem is under the
     rational-homeomorphism bound (`rational-homeomorphism-subgroups-have-exponential-wp`).
   - Šunić's groups are finite-state contracting groups, so they are under the same bound for every
     choice of polynomial.
   - So within this family, finite type and hardness exclude each other. Hard `G_ω` exist, since the
     complexity of `ω` passes to the word problem on words of length `2^n` probing level `n` (lane
     sketch). But
     their self-similarity uses infinitely many objects, while Li's finite-type theorem needs finitely
     many.

## Proof of item 2

- Grigorchuk's wreath recursion is `ψ(a)` = the swap, `ψ(b) = (a, c)`, `ψ(c) = (a, d)`,
  `ψ(d) = (1, b)`, with `b = cd`. Then:
  - `ψ(φ(a)) = ψ(a) ψ(c) ψ(a) = (d, a)`, the swap conjugating `(a, d)`;
  - `ψ(φ(c)) = ψ(b) = (a, c)`;
  - `ψ(φ(d)) = ψ(c) = (a, d)`.
- `φ(G) <= St_G(1)`, and first-coordinate projection is a homomorphism on `St_G(1)`. So
  `g ↦ pr_1 ψ(φ(g)) = θ(g)` is a homomorphism with the stated values on generators, and the second
  coordinate returns `g` on generators, hence on all of `G`.
- `θ(G) = ⟨a, d⟩` has order 8, since `ad` has order 4. So `ψ(φ(G)) <= D_8 × G`, which has infinite
  index in `G × G`.
- But `ψ(St_G(1))` has finite index in `G × G`, because `G` is regular branch. So `φ(G)` has infinite
  index in `St_G(1)`, hence in `G`.

## Proof of item 4 (finite-type clause)

- The sections of `s_ω` (`s ∈ {b, c, d}`) at the vertex `1^n` are `s_(σ^n ω)`, and the triple
  `(b_η, c_η, d_η)` determines `η`. So the states of the recursion are the `σ^n ω`, and there are finitely many iff `ω` is
  eventually periodic.
- This concerns the natural section structure only. Some other finite-type coding of `G_ω` is not
  excluded here; that is the open `computable-tree-groups-embed-in-fp-self-similar-groups`. The clause that eventually periodic `ω` gives contracting groups is Grigorchuk's
  length contraction, as in the cited node.

## Consequences

- **Both candidate families are closed as finite-type sources.**
  - Solvable candidates: KMS renormalization is dead (`kms-metabelian-layer-commensurations-have-finite-order`),
    and the Noetherian class is probably bounded (item 1).
  - Branch candidates: none is known to be finitely presented (item 3), and the Grigorchuk family
    is hard only with infinitely many types (item 4).
- **Where the branch group does become finitely presented, it sits at an emitter** (item 2). So the
  branch route to hardness leads back to gate (IE), like the Kazhdan inputs of the emitter lemma in
  `finite-type-e3-prime-hosts-carry-complexity-in-units`.
- **Remaining candidate for (SS-hard)_1.** An `F_2` group whose hardness sits in infinitely many
  "types" but whose commensuration still has finite data. Only a finitely presented branch group, or
  a non-branch group with a shrinking commensuration and a hard non-Noetherian layer, could do this.
  Neither is known.

## Lesson for general BH

**Hardness needs infinitely many types; finite presentation of self-similar data needs an emitter.**
In the known branch families, word-problem hardness comes from infinitely many self-similarity types
(non-periodic `ω`). With finitely many types the group is contracting and easy.

The one classical way to make a branch group finitely presented, Grigorchuk's substitution HNN
extension, is an ascending extension over an infinite-index subgroup. It turns the vertex group into
an infinite emitter.

So the two exits for hard inputs meet again: finite-type E3′ over hard units needs an object not
known to exist (a finitely presented group that is hard and shrinking), and the classical way to finitely present
branch self-similar data (the substitution HNN extension) passes through an emitter. (IE) is the decisive gate for both the Kazhdan and
the complexity sides.
