---
rg: 2
id: hard-quantum-rigid-free-minimal-z2-sfts-exist
kind: claim
title: For every recursive time bound some free minimal Z^2-SFT with finitely presented binary crossed product has a language not decidable within that bound
distinct_from:
  free-minimal-z2-sft-is-quantum-rigid: that asks for one quantum rigid free minimal Z^2-SFT over some field; this asks, over F_2, for such SFTs with arbitrarily hard languages, and implies that claim.
  minimal-free-z2-sfts-have-arbitrarily-hard-row-languages: that gives hard free minimal Z^2-SFTs with no presentation condition on the crossed product; this also requires the binary crossed product to be finitely presented, i.e. the SFT to be quantum rigid over F_2.
  decidable-algebras-embed-in-z2-sft-boundary-product-hosts: that is the universal embedding statement for boundary-product hosts; this is a consequence of it about the SFTs alone, with no embedding, and a refutation of this refutes that.
---

**OPEN.** Convention as in
`z2-sft-boundary-hosts-need-unboundedly-hard-sft-languages`: a `Z^2`-SFT `Ω`
is `T`-decidable if its set of globally admissible `n × n` patterns is decidable
in time `C·T(Cn) + Cn^2 + C` for some constant `C`.

**Statement.** For every recursive `T : N -> N` there is a free minimal
`Z^2`-SFT `Ω` such that
1. `B_Ω = LC(Ω, F_2) ⋊ Z^2` is finitely presented as an `F_2`-algebra
   (equivalently, by `sft-crossed-product-fp-iff-quantum-rigid`, `Ω` is
   `D`-quantum rigid over `F_2` for some `D`);
2. `Ω` is not `T`-decidable.

**Place in the graph.**
- It is a necessary condition for
  `decidable-algebras-embed-in-z2-sft-boundary-product-hosts` (route
  `hard-rigid-z2-sfts-from-z2-sft-boundary-host-embeddings`). It is the joint
  form of that target's prerequisites (Q) and (H): rigidity and hardness in the
  same shift.
- It implies `free-minimal-z2-sft-is-quantum-rigid`.
- Each half alone is known or reduced: hardness with freeness and minimality is
  `minimal-free-z2-sfts-have-arbitrarily-hard-row-languages` (ESTABLISHED), and
  rigidity alone is `free-minimal-z2-sft-is-quantum-rigid` (OPEN).

**Refutation shape.** A recursive `T` such that every free minimal `Z^2`-SFT
that is quantum rigid over `F_2` is `T`-decidable. For instance, a rigidity
mechanism that forces a hierarchical structure of bounded computational depth
would do. This would refute the boundary-product target by
`z2-sft-boundary-hosts-need-unboundedly-hard-sft-languages`.

**Why the two halves are in tension.** The known hard free minimal SFTs come
from Durand--Romashchenko simulation. That is a self-simulating
fixed-point tiling in which a computation runs inside every macro-tile.
Quantum rigidity needs every local quantum tiling to commute. Computation
zones carry long-range signals and are the natural place for walls. No
rigidity proof for any self-simulating tiling is known.
