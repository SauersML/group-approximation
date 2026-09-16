---
rg: 2
id: subcomplex-pi1-kernels-vanish-in-hyperlinear-quotients
kind: claim
title: In a contractible 2-complex, loops of a finite subcomplex that die in an H_1-injective finite enlargement die in every hyperlinear quotient
distinct_from:
  acyclic-subcomplex-of-contractible-2-complex-pi1-nonhyperlinear: that says a finite acyclic subcomplex has trivial or non-hyperlinear fundamental group; this is stronger in two ways. For acyclic K, every hyperlinear quotient of π_1(K) is trivial, even when π_1(K) is not hyperlinear. For K with H_1(K) ≠ 0, the kernel of π_1 into any H_1-injective finite enlargement dies in every hyperlinear group.
  kervaire-laudenbach-holds-for-hyperlinear: that is the Nitsche--Thom solvability theorem for systems over hyperlinear groups; this is its consequence for subcomplexes of contractible 2-complexes.
  whitehead-asphericity-conjecture: that asserts asphericity of subcomplexes; this constrains only homomorphisms from their fundamental groups to hyperlinear groups, and holds unconditionally.
  contractible-2-complex-subcomplexes-have-torsion-free-pi1: that says finite subcomplexes of contractible 2-complexes have torsion-free fundamental groups, which is open; this is an unconditional statement about hyperlinear quotients and does not exclude torsion.
artifacts:
  - research/artifacts/eilenberg-ganea-frontier-2026-09-16.md
---

Proved through `subcomplex-pi1-kernels-hyperlinear-quotients-proof`. Unreviewed. No novelty is
claimed. This is the argument of `acyclic-subcomplex-pi1-nonhyperlinear-proof`, with the system
pushed along an arbitrary homomorphism.

Let `Y` be a contractible 2-dimensional CW complex, and `K ⊆ Z ⊆ Y` finite connected subcomplexes
such that `H_1(K; Z) → H_1(Z; Z)` is injective. Put `N = ker(π_1(K) → π_1(Z))`.

- **(a)** Every homomorphism `ρ: π_1(K) → Q` to a hyperlinear (Connes-embeddable) group `Q`
  satisfies `ρ(N) = 1`.
- **(b)** If `H_1(K; Z) = 0`, then every homomorphism from `π_1(K)` to a hyperlinear group is
  trivial. In particular `π_1(K)` has no nontrivial finite quotient.

## Consequences

1. Taking `ρ = id` in (b) gives `acyclic-subcomplex-of-contractible-2-complex-pi1-nonhyperlinear`.
2. **Small-fiber images.** Let `L` be a finite simplicial complex with nontrivial hyperlinear
   `π_1(L)`, and `δ` a Lebesgue number of its open vertex-star cover. Suppose `g: |L| → |K|` is a
   surjection with fibers of diameter `< δ`, onto a finite subcomplex `K` of a contractible
   2-complex.
   - The coarse lifting lemma (artifact §2) gives `λ_*: π_1(K) → π_1(L)` onto.
   - So `H_1(K) ≠ 0` by (b).
   - By (a), for `β ≠ 1` in `π_1(L)`, the loop `g(β)` survives in every finite `H_1`-injective
     enlargement of `K` inside the complex.
3. **Shadows.** For the Poincaré-spine kernel `H_L`, if `gd H_L = 2`, then every large-scale shadow
   image `φ_v(S_(v,L))` in the proof of Bestvina--Brady Theorem 8.7 has nonzero `H_1`. See artifact
   §5.3.
