---
rg: 2
id: sp21-lattice-quotient-with-only-large-type-simple-images
kind: claim
title: A cocompact arithmetic Sp(2,1) lattice has hyperbolic Kazhdan quotients whose finite simple images are all large alternating or large-rank groups
distinct_from:
  sp21-lattice-hyperbolic-quotient-without-finite-quotients: that is the open target, a quotient with no finite quotient at all; this proves the same shape with every abelian, sporadic, congruence, bounded-rank and small simple image removed, so only large alternating and large-rank images can remain
  sp21-noncongruence-simple-kernels-separate-points: that is an open hypothesis on the kernels of the lattice's alternating and large-rank simple images; this is an unconditional quotient in which those images are the only ones left
  sp21-bounded-rank-simple-quotients-almost-all-congruence: that counts the non-congruence bounded-rank simple images of the lattice; this consumes that count, congruence openness and Olshanskii's theorem to remove all bounded-rank images from one hyperbolic quotient
artifacts:
  - research/artifacts/nrfh-kazhdan-quotientless-2026-09-12.md
---

**ESTABLISHED.** Let `Γ` be a torsion-free cocompact arithmetic lattice in
`Sp(2,1)`, set up as in `sp21-bounded-rank-simple-quotients-almost-all-congruence`:
`Γ <= G(O)` of finite index, with congruence completion `Γ̄`. For every `r >= 1`,
every `f >= 1` and every finite `B ⊂ Γ` there is an epimorphism `π : Γ ->> G`,
injective on `B`, such that:

1. `G` is torsion-free, non-elementary word-hyperbolic and Kazhdan, hence
   infinite;
2. `G` has no nontrivial finite quotient of order at most `f`;
3. `G` has no nontrivial congruence quotient, i.e. `ker π` is dense in `Γ̄`;
4. no finite simple quotient of `G` is abelian, sporadic, or of Lie type of Lie
   rank at most `r`.

By the classification, every finite simple quotient of `G` is therefore either an
alternating group or a group of Lie type of Lie rank `> r`. Its order is `> f`,
and its kernel in `Γ` is non-congruence. By (4) and finiteness of `Γ^ab`, `G` is
perfect.

**Distance to the target.** Such a `G` witnesses
`sp21-lattice-hyperbolic-quotient-without-finite-quotients` iff it has no
alternating and no rank-`> r` simple quotient. So what separates this statement
from that target is exactly those two families, now inside one hyperbolic
quotient rather than in the lattice.

**Contrapositive.** Suppose every hyperbolic group is residually finite. Then for
every `r`, `f` and `B` this `G` is residually finite. The simple quotients of its
finite quotients are all large alternating or large-rank groups with
non-congruence kernels, and these finite quotients alone separate the points of
`G`.

**Limit of the method.**
- Finitely many Olshanskii steps remove finitely many simple images by design.
- A family is removed wholesale only when each nontrivial normal subgroup lies in
  the kernels of finitely many of its members:
  - congruence images, by openness;
  - bounded-rank images, by
    `sp21-bounded-rank-simple-quotients-almost-all-congruence`.
- `tf-kazhdan-hyperbolic-alternating-kernels-not-separating` shows that (T),
  hyperbolicity and torsion-freeness do not give this for alternating images.
- An infinite strictly increasing chain of kernels has a limit that is not
  finitely presented, hence not hyperbolic.

See the artifact, §3.

Proof in `sp21-large-type-simple-images-quotient-proof`. The argument is Steps
1–3 of `quotientless-hyperbolic-via-sp21-noncongruence-separation`, with the
separation case dropped and small images added. No novelty claimed. Not
Lean-verified.
