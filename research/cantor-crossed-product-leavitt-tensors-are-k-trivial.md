---
rg: 2
id: cantor-crossed-product-leavitt-tensors-are-k-trivial
kind: claim
title: For a compact space crossed by a torsion-free Farrell–Jones group, the Leavitt tensor of the crossed product algebra has vanishing K-theory, with or without coherence
distinct_from:
  ara-cortinas-leavitt-tensor-k-theory-vanishes: that kills K(L_2 ⊗ B) for regular supercoherent B; this kills it for crossed products LC(X, k) ⋊ P, which are not even left coherent once P has a finitely generated subgroup that is not FP_infinity, using Farrell–Jones for P.
  regular-coherent-coefficients-kill-leavitt-tensor-k-theory: that needs the coefficient ring B to be regular coherent and gives degrees n >= 1; this assumes nothing about B beyond its crossed-product shape and gives every degree.
  leavitt-tensor-kills-k1-of-coefficient-matrices: that kills only the image of K_1(B) in K_1(B ⊗ L), for every B; this kills all of K_n(B ⊗ L) for these crossed products.
  minimal-cantor-crossed-product-k-theory-formula: that computes K_n(LC(X, F_q) ⋊ Z) itself, which is nonzero; this concerns the Leavitt tensor of the crossed product, where every K-group vanishes.
  coherent-flat-group-algebra-hosts-force-fp-infinity: that forbids left coherent hosts containing a group algebra flatly once the group contains Z wr Z; this shows that the K-theory condition on the Leavitt tensor survives for crossed products that fail coherence.
  leavitt-tensor-powers-have-vanishing-k-theory-in-all-degrees: that is the K-theory of the tensor powers of L; this is the K-theory of (LC(X, k) ⋊ P) ⊗ L, through a different coefficient ring and acting group.
artifacts:
  - research/artifacts/fjc-crossed-product-leavitt-hosts-2026-09-16.md
---

**ESTABLISHED (derivation from literature imports; unreviewed).** Let `k` be a
field and `L = L_k(1,2)`. Let `P` be a torsion-free group satisfying the
`K`-theoretic Farrell–Jones conjecture with additive categories as coefficients,
with respect to `VCyc`. Let `P` act by homeomorphisms on a nonempty compact
Hausdorff space `X`, and put `B = LC(X, k) ⋊ P`, with `(f g)(f' h) = f (f' ∘ g^−1) gh`.

1. `K_n(B ⊗_k L) = 0` for every `n ∈ Z`. In particular `K_1(B ⊗ L) = K_2(B ⊗ L) = 0`.
2. If `P` has a finitely generated subgroup that is not of type `FP_infinity`
   over `k`, then `B` is not left coherent.

**Why it matters.** Attempt 5 on `decidable-group-algebras-have-fp-central-simple-hosts`
shows that coherent hosts containing `F_2[G]` flatly fail once `G ⊇ Z wr Z`. It
concludes that a proof "must obtain the `K`-theory without regular coherence".
Part 1 does that for every crossed product of a compact space by a torsion-free
Farrell–Jones group. For such hosts the `K`-theory half of the target is
automatic, and only existence remains:
`decidable-group-algebras-have-fp-cantor-crossed-hosts`, route
`fp-central-simple-hosts-via-cantor-crossed-products`.

**Instances.** `P = Z^d` by
`virtually-poly-z-groups-satisfy-fjc-with-additive-coefficients`. So for every
`Z^d`-space `X`, including every free minimal `Z^2`-SFT, `K(LC(X, k) ⋊ Z^d ⊗ L) ≃ 0`.
Part 2 is illustrated in the artifact with `P = Z wr Z`, which is solvable. It
rests on Wegner's theorem for virtually solvable groups, checked at abstract
level only, and is not wired into any route.

**Consistency.** For `P = Z` and `X` an infinite minimal subshift over `F_2`,
`K_1(B) = Z` (`minimal-cantor-crossed-product-k-theory-formula`). Its image in
`K_1(B ⊗ L)` is zero by the corner swindle, which the artifact (Section 8)
records in every degree.

Proof: route `cantor-crossed-product-leavitt-tensors-are-k-trivial-proof`;
details in Sections 4 and 5 of the artifact.
