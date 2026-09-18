---
rg: 2
id: v-times-subshift-full-groups-locally-embed-in-v
kind: claim
title: Full groups of G_V x (Z ⋉ Y) with Y an irreducible subshift are locally embeddable into V, so they contain no infinite finitely presented simple Kazhdan group
distinct_from:
  periodic-approximable-subshifts-host-no-fp-simple-group: That approximates full groups of subshifts by finite symmetric groups and kills all finitely presented infinite simple subgroups; with the Cantor factor G_V the approximations land in Thompson's V, finitely presented simple subgroups exist (V itself), and the obstruction is Kazhdan versus Haagerup.
  v-times-shift-alternating-group-restrictions-are-simple: That proves the restriction quotients A(G|_{C x Y}) are simple; this shows that every host of that shape, for any irreducible Y, misses every infinite finitely presented simple Kazhdan group, so it cannot serve as an envelope route for Zaremsky 1.25.
  every-countable-group-lies-in-a-faithful-ha2-actor: That is the actor reduction for the twisted Brin–Thompson route; this is an obstruction to a different envelope family, Nekrashevych groups of V-times-subshift groupoids.
artifacts:
  - research/v-times-subshift-full-groups-locally-embed-in-v-proof.md
---

**ESTABLISHED** (proof artifact complete; referee pending).

**Setting.**
- `C = {0,1}^N` is the Cantor set, and `G_V` is the groupoid of germs of prefix
  replacements on `C`, so `[[G_V]] = V`.
- `Y ⊆ A^Z` is an infinite subshift over a finite alphabet. It is
  *irreducible*: for all `u, w` in `L(Y)` there is a word `v` with `uvw` in `L(Y)`.
  - This includes the full shift, all irreducible SFTs and sofic shifts, and
    every infinite minimal subshift.
- `G = G_V x (Z ⋉ Y)` acts on `C x Y`, and `[[G]]` is its topological full group.
  - It contains the alternating group `A(G)` and every restriction quotient
    `A(G|_{C x Y})` used in `uncountably-many-simple-fp2-via-v-times-shift-restrictions`.

**Theorem.** Let `Gamma ≤ [[G]]` be finitely generated.
1. *(LE-V)* For every finite `F ⊆ Gamma` there are `N ≥ 1` and a homomorphism
   `rho` from a free group onto a subgroup of the Higman–Thompson group
   `V_{2,N} ≅ V` that yields a partial homomorphism `F -> V` which is injective
   on `F`.
   - The homomorphism `rho` kills every relator of `Gamma` of length at most any
     prescribed bound.
   - So `Gamma` is locally embeddable into `V`.
2. If `Gamma` is finitely presented, then for every finite `F` there is a
   homomorphism `Gamma -> V` that is injective on `F`.
3. If `Gamma` is finitely presented and simple, then `Gamma` embeds in `V`.
4. If `Gamma` is finitely presented and Kazhdan, then `Gamma` is residually
   finite. If `Gamma` is in addition simple, then it is finite.

**Theorem′ (other acting groups; proof Step 6).** Items 1-4 hold for every
finitely generated subgroup of `[[G_V x (Delta ⋉ Y)]]`, for any finitely
generated `Delta` and any subshift `Y ⊆ A^Delta` with (PA*).
- (PA*) says two things:
  - free points are dense;
  - for any finite set of `K`-patterns of `Y` and any finite
    `B ⊆ Delta \ {e}`, some finite `Delta`-set `S` with an equivariant map
    `pi : S -> A^Delta` has all `K`-patterns in `L_K(Y)` and realises each given
    pattern at a point whose stabilizer misses `B`.
- (PA*) holds for:
  - infinite irreducible `Z`-subshifts;
  - full shifts over infinite residually finite groups;
  - topologically free minimal subshifts with (PA) in the sense of
    `periodic-approximable-subshifts-host-no-fp-simple-group`.
- For `Y = {0,1}^Z` we have `[[G]] ≤ 3V`, as noted in
  `v-times-shift-alternating-group-is-of-type-fp2`. So in this subgroup of
  `3V` every finitely presented Kazhdan subgroup is residually finite, and no
  infinite finitely presented simple Kazhdan group occurs. These are special
  cases of the open finiteness question for `nV`, `n ≥ 2`
  (`kazhdan-subgroups-of-brin-thompson-groups-are-finite`).

**Corollary (class-killing obstruction for Zaremsky 1.25).** No group of the form
`[[G_V x (Z ⋉ Y)]]` contains an infinite finitely presented simple Kazhdan
group, whatever the irreducible `Y` and the alphabet. The same holds for any
subgroup of such a group, including `A(G|_{C x Y})`.
- Such groups exist: the Kac–Moody lattice of
  `km-246-lattice-fp-simple-kazhdan-irs-rigid-for-q-ge-4`.
- The lattice `Lambda` is its own simple `FP_2` envelope. But every countable
  input containing it fails, for example `Lambda * H` with `H` not recursively
  presented.
  - For such inputs the envelope route "embed the input into a simple `FP_2`
    quotient `A(G|_{C x Y})`" fails for every `Y`, whether or not these groups
    are `FP_2`.
- More generally the route can only handle inputs whose finitely generated
  subgroups are all LE-V.
- Any positive answer to 1.25 needs, for such inputs, hosts that are not built
  this way.

**Exact break.**
- Irreducibility gives periodic points whose windows all lie in `L(Y)` and that
  contain any prescribed finite set of words.
- Running the finite rules of the generators on `C x Z/N` along such a point
  gives elements of `V_{2,N} ≅ V`.
  - Short relators still hold, because each rule only reads windows that occur
    in `Y`.
  - Short non-relators still act nontrivially, because a witness window is
    placed in the periodic point.
- `V` has the Haagerup property (`thompson-v-has-haagerup-property`), so its
  Kazhdan subgroups are finite.

**Dictionary (transplant from symbolic dynamics).**

| Symbolic dynamics | Envelope question |
|---|---|
| periodic approximation of a subshift | approximation of the envelope by `V` |
| LEF of Grigorchuk–Medynets | LE-V |
| language `L(Y)` | the relators the envelope can see |
| a strongly aperiodic subshift (no periodic approximations) | what an envelope for Kazhdan inputs needs |

By Theorem′, the only escape is a shift factor without (PA*). Over `Z`,
irreducible subshifts always have it. Over residually finite groups, full shifts
have it. A host for Kazhdan inputs therefore needs one of two things:
- a subshift with no periodic approximations, for example a strongly aperiodic
  `Delta`-subshift;
- an acting group with few finite quotients, for example a simple `Delta`,
  which has no nontrivial finite `Delta`-sets.

For hosts over the km-246 lattice itself the obstruction is vacuous, as it must
be.

**Proof.** See `research/v-times-subshift-full-groups-locally-embed-in-v-proof.md`.
