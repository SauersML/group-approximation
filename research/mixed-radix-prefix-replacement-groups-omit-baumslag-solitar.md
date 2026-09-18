---
rg: 2
id: mixed-radix-prefix-replacement-groups-omit-baumslag-solitar
kind: claim
title: Prefix-replacement groups of mixed-radix odometer spaces are locally finite or embed in a Higman-Thompson group, so none contains BS(1,p) for p >= 2, (Q,+), or Aff(Q)
distinct_from:
  aff-q-embeds-in-fp-simple-group: that is the open embedding question for Aff(Q); this excludes one natural host family designed for it (all rationals have finite factorial-base expansions).
  finite-state-mobius-pieces-see-finitely-many-primes: that bounds the primes seen by finite-state Mobius pieces on p-adic trees; this is about mixed-radix Cantor spaces with prefix replacements, where the failure is local finiteness or periodicity of the radix sequence.
---

**ESTABLISHED** (lane proof, elementary, not reviewed; no priority claimed).

## Motivation (the host this kills)

In the factorial base, every rational in [0,1) has a *finite* expansion
x = Σ_{n≥2} d_n/n!, 0 ≤ d_n < n. This is the mixed-radix analogue of dyadic rationals
in binary, which is why V-type groups contain the dyadic affine maps. The natural
candidate host for Aff(Q) is therefore a V-type group over the factorial odometer
space. This node shows that no prefix-replacement group over any mixed radix works.

## Setting

Let r = (r_1, r_2, …) with r_i ≥ 2, and let X_r = ∏_i Z/r_i. A cylinder [w] of depth k is fixed by
a word w ∈ ∏_{i≤k} Z/r_i. Write tail_k(r) = (r_{k+1}, r_{k+2}, …). A *prefix replacement*
[w] → [w'] (depths k, k') is wx ↦ w'x. It is a well-defined homeomorphism exactly when
tail_k(r) = tail_{k'}(r). G_r is the group of homeomorphisms of X_r that are piecewise prefix
replacements on a finite partition into cylinders.

## Statement

1. If r is not eventually periodic, G_r is locally finite.
2. If r is eventually periodic, with period block (r_{k0+1}, …, r_{k0+p}) and N = r_{k0+1}⋯r_{k0+p},
   then G_r embeds in the Higman–Thompson group V_{N,M}, where M is the number of depth-k0 cylinders.
3. In either case G_r contains no BS(1,m) with |m| ≥ 2. It also contains no (Q,+) and no Aff(Q).

## Proof

1. tail_k(r) = tail_{k'}(r) with k < k' says r_{j} = r_{j+(k'-k)} for all j > k, so r is eventually
   periodic. Hence, if r is not eventually periodic, every prefix replacement preserves depth.
   Refine the partition of g ∈ G_r to a common depth K. Then g permutes the finitely many depth-K
   cylinders and acts as the identity on tails. So every finitely generated subgroup lies in the
   finite group Sym(depth-K cylinders) for K large, and G_r is locally finite.
2. If r is eventually periodic, tail_k = tail_{k'} exactly when k, k' ≥ k0 and k ≡ k' mod p, or
   k = k'. Refine every cylinder of a partition to a depth ≥ k0 that is ≡ k0 mod p. Read each block of
   p digits past depth k0 as one N-ary digit and the first k0 digits as one of M roots. Then every
   element of G_r is a piecewise N-ary prefix replacement on M roots, i.e. an element of V_{N,M}, and
   the map is an injective homomorphism.
3. A locally finite group has no element of infinite order. V_{N,M} embeds in Thompson's V (standard;
   the Higman–Thompson groups embed in V_{2,1}; cited, not re-read at source). Cyclic subgroups of V are
   undistorted (`thompson-v-cyclic-subgroups-are-undistorted`), while ⟨a⟩ is exponentially distorted in
   BS(1,m), |m| ≥ 2. So BS(1,m) ⊄ G_r. And (Q,+) ⊄ V (survey Theorem 4.4, root obstruction O3 of
   `gl-n-q-embeds-in-fp-simple-group`). Aff(Q) ⊇ BS(1,2), so it is excluded too.

## Scope

- This kills the factorial-base prefix-replacement host (r_n = n + 1 is not eventually periodic,
  so G_r is locally finite), and every mixed-radix variant.
- Not excluded: hosts that change radix structure by non-prefix maps. Examples are finite-state
  digit reorderings between tails with the same radix multiset, or germ extensions of G_r by
  maps that are not prefix replacements. Any Aff(Q) host over a mixed-radix space has to use
  such maps at infinitely many depths.
