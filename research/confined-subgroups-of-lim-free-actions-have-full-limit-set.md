---
rg: 2
id: confined-subgroups-of-lim-free-actions-have-full-limit-set
kind: claim
title: If a group acts on a hyperbolic space with general type and topologically freely on the limit set, every confined subgroup has the full limit set and is lim-free
distinct_from:
  confined-subgroup-commutator-lemma: that is the Le Boudec--Matte Bon commutator lemma, which places part of a rigid stabilizer inside a confined subgroup when rigid stabilizers are nontrivial; this is the opposite, topologically free regime, where confined subgroups are forced to be geometrically large.
  rybak-general-type-limit-set-topologically-free-iff-mif: that turns a topologically free limit-set action into MIF; this shows that confined subgroups inherit such an action from the ambient group.
---

**ESTABLISHED** through `lim-free-confined-subgroups-full-limit-set-proof` (direct
proof). Not independently reviewed, and no novelty is claimed.

**Statement.** Let a group `G` act by isometries on a hyperbolic space `S` with an
action of general type, and suppose the induced action on `Λ_S(G)` is topologically
free. Let `H ≤ G` be confined. Then:
- `H` acts on `S` with general type;
- `Λ_S(H) = Λ_S(G)`;
- the action of `H` on `Λ_S(H)` is topologically free and minimal.

So `H` is lim-free in Rybak's sense, through the same space `S`.

**More precisely,** a subgroup `K ≤ G` is not confined if any of the following holds:
- `K` has a bounded orbit on `S`;
- `Λ_S(K) ≠ Λ_S(G)`;
- `K` fixes a point of `Λ_S(G)`.

**Definitions.**
- **Confined** (Le Boudec--Matte Bon, Ann. H. Lebesgue 5 (2022), §2.2): some finite
  `P ⊂ G \ {1}` meets `gHg^{-1}` for every `g ∈ G`.
- **Topologically free, limit set, lim-free:** as quoted in
  `rybak-general-type-limit-set-topologically-free-iff-mif`.

**Related literature.** Choi--Gekhtman--Yang--Zheng, *Confined subgroups in groups
with contracting elements*, arXiv:2405.09070, TeX on MSI, Corollary `FullLimitSet`
(l.2683--2685): "In the setting of Theorems \ref{ConInHorLimitSet} or
\ref{ConInHorLimitSet2}, if $H$ is a subgroup of $\Gamma$, then
$[\pG] = [\Lambda (Ho)]$."
- **Their setting.** Their standing assumption (l.870) is that "$\Gamma$ acts
  properly on $\U$", and l.954 takes a proper geodesic metric space.
- **Why it doesn't apply here.** The action used downstream, a Kac--Moody lattice on
  the injective hull of a curtain model, has infinite point stabilizers on a space
  that need not be proper.
- **What replaces properness.** The argument here uses topological freeness on the
  limit set instead. It is elementary and needs only finitely many elements avoided,
  with no measure or Baire category input.

**Trust surface.** The standard facts about hyperbolic spaces used in the proof are
those quoted in Rybak (arXiv:2605.14159v3) from Gromov, Hamann and
Das--Simmons--Urbański, listed as (F1)--(F7) in the route. They were not re-read at
the primary sources.

**Consumer.** `kac-moody-lattice-confined-subgroups-are-lim-free-and-mif`.
