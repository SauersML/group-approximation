---
rg: 2
id: thompson-f-is-not-co-amenable-in-its-known-nonamenable-hosts
kind: claim
title: Thompson's group F is not co-amenable in T, in V, in the Lodha--Moore group, or in Monod's groups H(A)
distinct_from:
  jones-subgroup-is-co-amenable-in-thompson-f: that asks whether a subgroup of F is co-amenable in F; this is about F as a subgroup of larger non-amenable groups.
  thompson-t-orbits-carry-no-invariant-means: that is about invariant means on T-orbits of points; this is about the coset space of F in T and in three other hosts, and its main new case (the Lodha--Moore group) is measured, not topological.
  thompson-f-interval-orbit-relation-is-hyperfinite: that kills the Monod mechanism on F itself; this kills it on every overgroup acting on the line in which F would be co-amenable.
  thompson-f-is-a-subgroup-of-lodha-moore-group: that embeds F in the Lodha--Moore group; this shows the embedding is not co-amenable, so non-amenability of the host cannot descend to F.
artifacts:
  - research/co-amenable-subgroups-transfer-hyperfinite-orbit-relations.md
---

**ESTABLISHED.** If `H ≤ G` is co-amenable and `G` is non-amenable, then `H` is non-amenable
(compose the invariant mean on `G/H` with a mean on `H`). "Show that `F` is co-amenable in a
group already known to be non-amenable" is therefore a route to
`thompson-f-is-not-amenable`. This claim kills it for the four families of non-amenable
overgroups of `F` in the literature.

1. **Circle hosts.** Let `F` act on `S^1 = [0,1]/(0∼1)` by its standard action, fixing `0`.
   Let `F ≤ G ≤ Homeo(S^1)` with `G` not fixing `0`. Then `F` is not co-amenable in `G`. In
   particular this holds for Thompson's `T`, which contains the rotation `t ↦ t + 1/2`.
2. **Cantor hosts.** Let `F` act on `2^N` by prefix replacement. Let `F ≤ G ≤ Homeo(2^N)` with
   `G·0^∞ ⊄ {0^∞, 1^∞}` and `G·1^∞ ⊄ {0^∞, 1^∞}`. Then `F` is not co-amenable in `G`. In particular
   this holds for Thompson's `V`, which contains the swap `0ξ ↔ 1ξ`.
3. **The Lodha–Moore group.** `F = ⟨a, b⟩` is not co-amenable in `G_0 = ⟨a, b, c⟩`
   (arXiv:1308.4250).
4. **Monod's groups.** Let `A < R` be a countable subring with `A ≠ Z` and `0 ∈ P_A` (e.g.
   `A = Z[1/n]` for `n ≥ 2`, or `A = Z[√2]`). Then `F = P(Z)` lies in `H(A)` and is not
   co-amenable there.

**The invariant, and where every member dies.** A co-amenable subgroup passes its amenable
witnesses up to the host:
- a compact `G`-space carrying an `H`-invariant probability carries a `G`-invariant one
  (Eymard);
- a nonsingular `G`-space on which `R_H` is hyperfinite has `R_G` hyperfinite
  (`co-amenable-subgroups-transfer-hyperfinite-orbit-relations`).

Every host above is proved non-amenable on a space where `F` itself is amenable.
- In cases 1–2 the witness is the boundary action, where `F` has a fixed point.
- In cases 3–4 the witness is the Lebesgue orbit relation on the line (Carrière–Ghys via
  Monod). There the relation of `F` is hyperfinite by
  `thompson-f-interval-orbit-relation-is-hyperfinite`.

So each proof of the host's non-amenability, fed through co-amenability, contradicts itself.
A host route can succeed only with a non-amenability witness for `G` whose restriction to `F`
is already non-amenable, which is a direct certificate for `F`.

**Not covered.**
- Hosts whose non-amenability is witnessed elsewhere, for example by a free subgroup acting
  on no space where `F` has an invariant measure or a hyperfinite relation.
- Other natural overgroups: `nV` for `n ≥ 2`, and the group `⟨t ↦ t + 1/2, b⟩` mentioned in
  Lodha–Moore l.136–138.

Proof route: `thompson-f-not-co-amenable-in-known-hosts-proof`.
