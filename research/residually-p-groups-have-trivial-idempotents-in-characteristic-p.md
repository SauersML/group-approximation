---
rg: 2
id: residually-p-groups-have-trivial-idempotents-in-characteristic-p
kind: claim
title: Group rings of residually finite p-groups over fields of characteristic p have only trivial idempotents
distinct_from:
  kaplansky-idempotent-conjecture-characteristic-p: that is the conjecture for all torsion-free groups; this proves the idempotent statement for residually finite p-groups, with or without torsion.
  p-adic-analytic-torsion-free-groups-satisfy-strong-atiyah: that proves the stronger domain property for subgroups of torsion-free p-adic congruence kernels; this needs only residual p-finiteness and says nothing about zero divisors.
  residually-p-kernels-preserve-modular-stable-finiteness: that extends stable finiteness across residually-p kernels; this is the idempotent statement for residually-p groups themselves.
---

Let `p` be a prime, `K` a field of characteristic `p`, and `G` a residually
finite `p`-group: every nontrivial element survives in some quotient `G/N`
that is a finite `p`-group. Then `K[G]` has no idempotents other than `0` and `1`.

ESTABLISHED through `residually-p-trivial-idempotents-proof`. The argument is
elementary and presumably folklore; no novelty is claimed and no source was
located.

**Instances.**
- Free groups; residually torsion-free nilpotent groups. These already have
  unique products.
- The Promislow group `P` over characteristic `2`. The lattice `Z^3 <= P` is
  normal of index `4` and `P` acts on it by integer matrices. So `2^k Z^3` is
  normal in `P`, `P/2^k Z^3` is a finite `2`-group, and these subgroups intersect
  trivially.
- Groups with `p`-torsion. The Grigorchuk group over characteristic `2`, and
  Gupta--Sidki `p`-groups over characteristic `p`, are residually `p` through
  their level-stabilizer quotients, which are iterated wreath products of
  `Z/p`. So nontrivial idempotents in positive characteristic need torsion of
  order prime to `p`, or a group that is not residually `p`.
