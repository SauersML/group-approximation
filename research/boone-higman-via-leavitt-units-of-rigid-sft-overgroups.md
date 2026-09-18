---
rg: 2
id: boone-higman-via-leavitt-units-of-rigid-sft-overgroups
kind: route
title: Put the group inside the acting group of a finitely presented free minimal crossed product, then pass to the units of its Leavitt tensor
target: boone-higman-conjecture
requires:
  - decidable-groups-lie-in-fp-free-minimal-crossed-products
  - free-minimal-cantor-crossed-products-are-central-simple
  - free-action-leavitt-tensor-hosts-have-trivial-k1-k2
  - leavitt-tensor-hosts-acyclic-steinberg-and-fp
  - central-simple-leavitt-tensor-unit-groups-are-simple
---

**Compared with neighbouring routes.**
- `boone-higman-via-v-times-aperiodic-sft-full-groups` needs P1 and the group-side finiteness P2 for
  every minimal free SFT. This route needs one quantum rigid shift over one overgroup, implied by P1
  and P2, and replaces P2 by a ring-side K-theory statement.
- `boone-higman-via-units-of-cantor-crossed-leavitt-tensors` needs a torsion-free Farrell-Jones acting
  group and an unspecified embedding of `G` in the unit group. This route takes `G` inside the acting
  group, allows torsion, and pays with the open K-theory premise for free actions.

Let `G` be finitely generated with solvable word problem. Put `L = L_(F_2)(1,2)`.

1. `decidable-groups-lie-in-fp-free-minimal-crossed-products` gives a finitely generated `Λ >= G`
   and a free minimal subshift `X` with `B = LC(X, F_2) ⋊ Λ` finitely presented.
2. `free-minimal-cantor-crossed-products-are-central-simple` makes `B` simple with `Z(B) = F_2`.
3. **`G` embeds in `(B ⊗ L)^x`.**
   - `λ -> u_λ` is a homomorphism `Λ -> B^x`. It is injective, because the `u_λ` form a free
     `LC(X, F_2)`-basis and `X ≠ ∅`.
   - `b -> b ⊗ 1` is a unital injective ring map `B -> B ⊗ L`, since `L ≠ 0` over a field.
   - So `G <= Λ <= B^x <= (B ⊗ L)^x`.
4. `free-action-leavitt-tensor-hosts-have-trivial-k1-k2` gives `K_1(B ⊗ L) = K_2(B ⊗ L) = 0`.
5. `leavitt-tensor-hosts-acyclic-steinberg-and-fp`(3) makes `(B ⊗ L)^x` finitely presented, since `B`
   is simple, unital and finitely presented. This step is conditional on Khanh arXiv:2609.08428v1.
6. `central-simple-leavitt-tensor-unit-groups-are-simple`(2) makes `(B ⊗ L)^x` simple.

So `G` embeds in a finitely presented simple group. ∎

## What the decomposition changes

- **P2 leaves the critical path.** `quantum-rigid-sfts-over-fp-groups-have-fp-crossed-products` and
  `fp-v-times-subshift-full-groups-force-quantum-rigidity` give P1 ∧ P2 ⇒ (E) ⇒ P1. The V-times route
  asks the group `A(T)` to be finitely presented for every minimal free SFT. Here only one quantum rigid
  shift over one overgroup is needed, and the finiteness is ring-side, where rigidity is proved to
  suffice over every finitely presented group.
- **The converse of the necessity theorem is not needed.** The V-times route has to show that quantum
  rigidity (or more) makes `A(T)` finitely presented. That converse is recorded as "Not attempted" on
  `v-times-minimal-free-sft-alternating-full-groups-are-fp`. Here the ring-side converse is the
  established claim `quantum-rigid-sfts-over-fp-groups-have-fp-crossed-products`.
- **Independent failure points.**
  - (E) is dynamical and can fail by an input with no rigid overgroup shift.
  - (K) is K-theoretic and can fail by a free action with nonzero `K_1(B ⊗ L)`.
  - The Khanh transfer can fail at its own import.
  - (E) and (K) share no hypothesis, since (K) is asserted for every free action.
- **Relation to the older Leavitt route.** If `Λ` in (E) is torsion-free Farrell-Jones, (K) is the
  established `cantor-crossed-product-leavitt-tensors-are-k-trivial`. Steps 1-3 then prove
  `decidable-groups-embed-in-cantor-crossed-leavitt-tensor-units` for torsion-free inputs. Torsion in
  `G` forces torsion in `Λ`, which is why (K) is stated for free actions. The trace detector shows
  freeness cannot be dropped.

## Status

**OPEN.** Open prerequisites: (E) `decidable-groups-lie-in-fp-free-minimal-crossed-products` and (K)
`free-action-leavitt-tensor-hosts-have-trivial-k1-k2`. Step 2 is established here. Steps 5-6 are
established (unreviewed), with step 5 conditional on Khanh.
