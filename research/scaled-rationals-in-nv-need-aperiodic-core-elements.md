---
rg: 2
id: scaled-rationals-in-nv-need-aperiodic-core-elements
kind: claim
title: A copy of Q in nV scaled by a rational a != ±1 consists of elements with zero periodic exponents and an aperiodic core, so the odometer copy of Q in 2V is scaled by nothing
distinct_from:
  bs-kl-images-in-brin-thompson-groups-have-open-periodic-sets: that is the constraint on one element conjugate to a proper power; this claim applies it to every element of a scaled copy of Q and rules out the known copy.
  rational-stepping-stones-in-nv-need-bs12-or-heisenberg: that reduces the stepping stones to BS(1,2) in nV; this claim says which copies of Q can serve as their unipotent part.
  rationals-embed-in-brin-thompson-group-2v: that constructs the odometer copy; this claim shows no element of any nV normalizes it by a nontrivial scaling.
artifacts:
  - research/artifacts/gq-bt-kojima-mechanism.md
---

**ESTABLISHED** through `scaled-rationals-in-nv-need-aperiodic-core-elements-proof`
(lane proof, not independently reviewed).

**Statement.** Let `n >= 1`, let `D <= nV` be isomorphic to `(Q,+)`, and let
`f ∈ nV` normalize `D`, acting on it as multiplication by `a = p/q ∈ Q^x` in
lowest terms, with `a != ±1`.
1. Every `d ∈ D \ {1}` satisfies the conclusions of
   `bs-kl-images-in-brin-thompson-groups-have-open-periodic-sets`:
   - every periodic point has exponent vector 0;
   - `Per(d)` is open, and some power of `d` is the identity on a brick around
     each periodic point;
   - `C^n \ Per(d)` is a nonempty closed `d`-invariant set without periodic
     points.
   - if `a ∈ Z`, then `L(d^N) <= c_d (1 + log_2 |N|)` for all `N != 0`
     (`bs12-images-in-nv-have-logarithmic-table-length`). So every element of `D` is
     logarithmically distorted in its table length.
2. **The known copy is not scaled.** Let `R = ∪_k <s_k> <= 2V <= nV` be the
   odometer copy of `rationals-embed-in-brin-thompson-group-2v-proof`. No
   `f ∈ nV` acts on `R` as multiplication by any `a ∈ Q^x \ {±1}`. The same
   holds for every copy of `Q` in `nV` containing an element with a periodic
   point of nonzero exponent. That includes every copy built by a register on an
   element `g × id` such that `g ∈ V` has such a point.

**Consequence for the root.** In an embedding of `Aff(Q)` or `GL_n(Q)`
(`n >= 2`) into some `nV`, the unipotent `(Q,+)` goes to a copy of `Q` scaled by
every prime. So it must be made only of aperiodic-core elements, and it cannot be
the odometer copy. This sharpens
`rational-stepping-stones-in-nv-need-bs12-or-heisenberg`. Such a copy would come
with a witness for `bs12-embeds-in-brin-thompson-2v`, and Kojima--Sheng-type
registers must then be built on a base like Callard--Salo's distortion element,
not on an element of `V × id`.
