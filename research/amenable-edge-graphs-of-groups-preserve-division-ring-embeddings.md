---
rg: 2
id: amenable-edge-graphs-of-groups-preserve-division-ring-embeddings
kind: claim
title: Division-ring embeddability of group rings is closed under graphs of groups with amenable edge groups, with no hypothesis on the vertex division rings
distinct_from:
  fsp-graph-of-rings-and-linnell-extension-imports: that needs locally indicable vertex groups with Hughes-free division rings, so that compatibility follows from Hughes' uniqueness; this allows arbitrary vertex groups and arbitrary vertex division rings, and gets compatibility from the Ore localisation of the amenable edge group ring.
  product-of-trees-lattices-embed-in-division-rings: that is the free-vertex, arbitrary-edge case; this is the arbitrary-vertex, amenable-edge case, and it mixes vertex groups that are not locally indicable, such as the Promislow group.
  kaplansky-zero-divisor-conjecture: that is the conjecture; this gives a permanence theorem that excludes every host splitting over amenable subgroups into division-ring-embeddable pieces, and a new class of groups satisfying it.
---

**ESTABLISHED** by [[amenable-edge-division-ring-embeddings-proof]]. Not yet independently re-derived.

Let `k` be a field and let `G` be the fundamental group of a graph of groups `(G_v, G_e)` in which every edge group
`G_e` is amenable and every vertex group ring `k[G_v]` embeds in some division ring `D_v`. The embeddings are
arbitrary: no Linnell, Hughes-free or uniqueness condition. Then `k[G]` embeds in a division ring.

**Permanence form.** Let `E_k` be the class of groups `G` such that `k[G]` embeds in a division ring. Then `E_k` is
closed under fundamental groups of graphs of groups with amenable edge groups, including amalgams and HNN extensions
over amenable subgroups. It contains:
- torsion-free elementary amenable groups (Kropholler--Linnell--Moody);
- graphs of free groups and torsion-free lattices in products of two trees
  (`product-of-trees-lattices-embed-in-division-rings`);
- virtually special and 3-manifold groups (Fisher--Sanchez-Peralta);
- Higman's group (`higman-group-algebras-embed-in-division-rings`).

**A new class.** Let `Lambda` be a Burger--Mozes torsion-free finitely presented simple lattice, `P` the Promislow
group, and `G = Lambda *_Z P` for any infinite cyclic subgroups. Then `k[G]` embeds in a division ring over every
field. The group `G` is torsion-free and finitely presented, and it is:
- not locally embeddable into unique-product groups, since it contains `P`;
- not locally embeddable into amenable groups;
- not locally embeddable into residually finite groups.

Hence it is not in any of the known cases listed in `kaplansky-zero-divisor-conjecture`, in any characteristic.

**Obstruction for hosts.** If `k[G]` has a zero divisor and `G` splits over amenable subgroups, then some vertex group
ring `k[G_v]` does not embed in a division ring. For example, the vertex group cannot be a torsion-free elementary
amenable group, a graph of free groups, or a special group. Splitting over amenable pieces is a dead end for building
hosts out of these blocks.

The theorem is not Lewin's (Trans. AMS 192 (1974)). That one needs a common normal subgroup with an Ore group ring.
