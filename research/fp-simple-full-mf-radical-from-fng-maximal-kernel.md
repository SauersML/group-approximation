---
rg: 2
id: fp-simple-full-mf-radical-from-fng-maximal-kernel
kind: route
title: Divide the defect-saturation group by a finitely normally generated maximal kernel
target: fp-simple-full-mf-radical-group
requires: [defect-saturation-full-mf-radical, defect-saturation-has-fng-maximal-kernel, fp-quotient-iff-kernel-finitely-normally-generated, mf-radical-functoriality]
artifacts:
  - research/artifacts/boone-higman-mf-radical-bridge-2026-09-11.md
---

Let `G` be the group of `defect-saturation-full-mf-radical`: two-generated,
finitely presented, torsion-free, property `(T)`, acylindrically hyperbolic,
with every homomorphism to an MF group trivial, that is `Rad_MF(G)=G`.

By `defect-saturation-has-fng-maximal-kernel` choose a maximal proper normal
subgroup `M <| G` that is finitely normally generated, and put

```text
K = G / M,      pi : G ->> K.                                (FNG1)
```

**`K` is simple.** The normal subgroups of `K` correspond to the normal
subgroups of `G` containing `M`; maximality of `M` leaves only `M` and `G`,
so `K` has only the trivial and the full normal subgroup. `K` is nontrivial
because `M` is proper.

**`K` is finitely presented.** `G` is finitely presented and `M` is finitely
normally generated, so this is the forward direction of
`fp-quotient-iff-kernel-finitely-normally-generated`.

**`K` has full MF radical.** Apply `mf-radical-functoriality` to `pi`:

```text
pi(Rad_MF(G)) <= Rad_MF(K).                                  (FNG2)
```

`Rad_MF(G)=G` and `pi` is onto, so the left side is `pi(G)=K`, giving
`Rad_MF(K)=K`. Equivalently, every homomorphism from `K` to an MF group is
trivial: it would pull back along `pi` to a homomorphism from `G` to that MF
group, which is trivial, and `pi` is surjective.

So `K` is a finitely presented simple group with full MF radical. `∎`

## Why this route is not the target restated

The route consumes one open input, and that input is a statement about the
normal lattice of a single explicitly presented group — a different kind of
object from the existence statement it feeds. Everything else in the
derivation is already established. The route also does not pass through
Boone--Higman, so together with `fp-simple-full-mf-radical-from-boone-higman`
it gives the target two independent attacks: one that assumes a famous
conjecture and one that asks a concrete normal-lattice question about a group
this repository built.
