---
rg: 2
id: torsion-kk-identity-uhf-proof
kind: route
title: Invert the order in KK of the UHF factor and use bilinearity of the exterior product
target: torsion-kk-identity-dies-after-uhf-absorption
requires: [uct-class-permanence-properties, coprime-uhf-stabilizations-detect-uct]
artifacts:
  - research/artifacts/stw-uct-reduction-map-2026-09-11.md
---

Put `M = M_(P^∞)` and `R = Z[P^(-1)]`, so `K_0(M) = R` and `K_1(M) = 0`.

1. `M` is AF, so it satisfies the UCT (items 3--4 of
   `uct-class-permanence-properties`).  Both Ext terms in its UCT sequence
   vanish because `K_1(M) = 0`, so `KK(M, M) → Hom(R, R)` is an isomorphism.  It
   is multiplicative for the Kasparov product, since the map is induced
   functorially on K-theory.  Every group endomorphism of `R` is multiplication
   by an element of `R`, so `KK(M, M) ≅ R` as rings, with `[id_M] ↦ 1`.
2. Every prime divisor of `n` lies in `P`, so `n` is a unit of `R`.  Pick
   `u ∈ KK(M, M)` with `n · u = [id_M]`.
3. The exterior Kasparov product `KK(A, A) × KK(M, M) → KK(A ⊗ M, A ⊗ M)` is
   bilinear and sends `([id_A], [id_M])` to `[id_(A⊗M)]`.  Hence
   `[id_(A⊗M)] = [id_A] ⊗ (n · u) = (n · [id_A]) ⊗ u = 0`.
4. So `A ⊗ M` is KK-equivalent to the zero algebra, which is commutative, and it
   satisfies the UCT (item 1 of `uct-class-permanence-properties`).

The filter consequences follow from the definition of `𝒫(A)` and the
"at most one prime" clause of `coprime-uhf-stabilizations-detect-uct`.
