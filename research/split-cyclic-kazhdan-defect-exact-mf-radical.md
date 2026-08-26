---
rg: 2
id: split-cyclic-kazhdan-defect-exact-mf-radical
kind: claim
title: A sofic Kazhdan defect kernel gives an exact MF radical over Z
distinct_from:
  normal-kazhdan-defect-non-mf: That proves only the lower inclusion of a normal Kazhdan subgroup in the MF radical; this adds a faithful MF quotient, the split-Z geometry, finite presentation, torsion-freeness, and soficity.
  universal-mf-quotient: That identifies the quotient after the radical is known; this computes the radical from a compression defect and a concrete faithful quotient.
  mf-not-closed-under-integer-extensions: That records an integer extension which destroys MF but does not impose torsion-freeness, property (T) of the kernel, or an exact radical computation.
  finitely-generated-rf-automorphism-mapping-torus-is-rf: That gives the complementary obstruction: residual finiteness of the kernel makes an automorphism mapping torus MF, so the nontrivial-defect hypotheses here cannot then hold.
artifacts:
  - GroupApproximation/Sofic/NormalKazhdanMFRadical.lean
  - GroupApproximation/Sofic/SoficByAmenablePermanence.lean
  - GroupApproximation/Algebra/HNNFinitePresentation.lean
---

Let `K` be a finitely presented, torsion-free, sofic group with property
`(T)`, let `phi in Aut(K)`, and put

```text
G = K semidirectProduct_phi Z.
```

Suppose `G` contains a finitely generated Kazhdan subgroup `L` carrying a
one-sided compression configuration for which the intrinsic compression
defect is exactly the canonical kernel:

```text
D_G(L) = K x {0}.                                      (SCZ1)
```

Then

```text
G is finitely presented, torsion-free, sofic and hyperlinear,
Rad_MF(G) = K x {0},
G/Rad_MF(G) ~= Z.                                      (SCZ2)
```

If `K` is nontrivial, `G` is non-MF.  Every homomorphism from `G` to a
countable MF group factors uniquely through the exponent map `G->Z`; hence
the complete MF-target representation functor of `G` is that of `Z`.

If one element normally generates `K` inside `K`, the same element normally
generates `Rad_MF(G)` inside `G`.
