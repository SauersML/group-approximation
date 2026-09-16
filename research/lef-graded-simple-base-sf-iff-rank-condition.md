---
rg: 2
id: lef-graded-simple-base-sf-iff-rank-condition
kind: claim
title: A ring strongly graded by an LEF group over a simple identity component is stably finite iff it has the rank condition
distinct_from:
  rank-condition-rings-have-weakly-finite-images: that is Malcolmson's theorem for arbitrary rings, rank condition iff a nonzero weakly finite image, where the gap to stable finiteness of the ring itself stays open (Toeplitz algebra); this closes that gap for strongly LEF-graded rings with simple base, using the absorption embedding into R[Gamma].
  lef-group-rings-over-stably-finite-rings-are-stably-finite: that is about ordinary group rings R[A] over a stably finite R; this handles cocycle-twisted and strongly graded rings, which are not group rings, and reaches them from any weakly finite image through that result.
  anti-central-rank-condition-gives-weakly-finite-image: that produces a weakly finite image of one ternary Leavitt summand, a non-LEF setting where no route back to stable finiteness exists; this proves stable finiteness itself from the rank condition, over LEF gradings.
  simple-ring-stably-finite-iff-unit-not-paradoxical: that treats simple rings, the trivial grading, through paradoxicality and states on V(R); this allows any LEF grading group over a simple identity component, where the ring itself need not be simple, and adds the rank condition and weakly finite images.
artifacts:
  - research/artifacts/deligne-twisted-sf-rank-condition-dichotomy-2026-09-16.md
---

Let `Gamma` be a locally embeddable into finite groups (LEF) group, and `A = ⊕_(g in Gamma) A_g` a unital
ring with `A_g A_h = A_(gh)` for all `g, h` (strongly graded), whose identity component `A_1` is a simple
ring. Rings, homomorphisms and subrings are unital, and "weakly finite" means stably finite (`XY = I_n`
implies `YX = I_n` for every `n`). The following are equivalent:
1. `A` is stably finite;
2. `A` has a nonzero weakly finite homomorphic image;
3. `A` satisfies the rank condition: no `XY = I_(n+1)` with `X` of size `(n+1) x n` and `Y` of size
   `n x (n+1)`;
4. `(K_0(A), [A])` admits a state;
5. no matrix ring `M_n(A)` is properly infinite.

**Instances.**
- Every twisted group algebra `F^alpha[Gamma]` of an LEF group over a field, with any 2-cocycle `alpha`. In
  particular this covers every twisted group algebra of a residually finite group.
- Crossed products over simple rings.

**Mechanism.**
- **Absorption.** For `phi : A -> R` unital with `R != 0`, simplicity of `A_1` and strong grading make
  `phi` injective on every `A_g`. Then `Sigma x_g -> Sigma phi(x_g) g` embeds `A` unitally in the ordinary
  group ring `R[Gamma]`.
- **2 => 1.** For weakly finite `R`, the group ring `R[Gamma]` is stably finite over an LEF group, so its
  subring `A` is too.
- The remaining implications are general ring theory (artifact Sections 1–2).

**Hypotheses are needed.** Without strong grading over a simple base, 3 does not imply 1: the Toeplitz
algebra `K<x, y | yx = 1>` has the rank condition and is not directly finite.

Proof: route `lef-graded-simple-base-sf-iff-rank-condition-proof`.
