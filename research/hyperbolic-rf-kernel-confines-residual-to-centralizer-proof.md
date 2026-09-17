---
rg: 2
id: hyperbolic-rf-kernel-confines-residual-to-centralizer-proof
kind: route
title: Act on characteristic finite images of the kernel, then use that infinite normal subgroups of hyperbolic groups have finite centralizers
target: hyperbolic-rf-kernel-confines-residual-to-centralizer
requires: []
---

Throughout, `G` is non-elementary word-hyperbolic, `N ⊴ G` is infinite and
finitely generated, and `R(X)` is the intersection of the finite-index
subgroups of `X`.

## Step 0: characteristic finite images

Let `M ⊴ N` have finite index `m`.

- **The core is characteristic.** Since `N` is finitely generated, it has
  only finitely many subgroups of index at most `m`. Their intersection
  `M_c` is characteristic in `N` and of finite index, and `M_c ⊆ M`.
- **A finite image of `G`.** Conjugation by `G` preserves `N`, hence it
  preserves `M_c`. This gives a homomorphism `α_M : G -> Aut(N/M_c)` whose
  target is finite, so `ker α_M` has finite index in `G`.
- **The kernel.** `g in ker α_M` iff `g x g^(-1) x^(-1) in M_c` for all
  `x in N`.

No hypothesis on `G/N` is used here or anywhere below.

## Step 1: kernel trace (item 1)

Let `n in R(G) ∩ N`.

- For every finite-index `M ⊴ N`, the element `n` lies in the finite-index
  subgroup `ker α_M`. So `[n,x] in M_c ⊆ M` for every `x in N`.
- Intersecting over all such `M` gives `[n,x] in R(N)`, because every
  finite-index subgroup of `N` contains a finite-index normal one.

Hence `n in Z_f(N)`, which is the preimage of `Z(N/R(N))`.

## Step 2: finite centralizer (item 2)

- **A loxodromic in `N`.** Torsion subgroups of hyperbolic groups are finite,
  so the infinite subgroup `N` contains an element `g` of infinite order. In
  a hyperbolic group `g` is loxodromic, and `C_G(g)` is virtually cyclic.
- **The centralizer is virtually cyclic and normal.** `C_G(N) ⊆ C_G(g)`, so
  `C_G(N)` is virtually cyclic. It is normal, because `N` is normal.
- **It is finite.** Suppose `C_G(N)` is infinite. It then contains a
  loxodromic `h`, and its limit set is the two-point set `{h^+, h^-}`. That
  set is invariant under `G`, because `C_G(N)` is normal. A non-elementary
  hyperbolic group has no finite orbit on its Gromov boundary, which is a
  contradiction.

## Step 3: confinement (item 3)

Assume `N` is residually finite, and let `g in R(G)`. Suppose `g` does not
centralize `N`.

- Choose `x in N` with `y = g x g^(-1) x^(-1) != 1`. Here `y in N`, since `N`
  is normal.
- By residual finiteness of `N`, choose a finite-index `M ⊴ N` with
  `y not in M`. Then `y not in M_c`, so `α_M(g)` moves the coset `x M_c`.
- So `α_M(g) != 1`. But `ker α_M` is a finite-index subgroup of `G`, and
  `g in R(G)`, which is a contradiction.

Therefore `R(G) ⊆ C_G(N)`, and by Step 2 `R(G)` is finite. Equivalently, `G`
modulo the finite normal subgroup `C_G(N)` embeds in `Aut(N)`. That group is
residually finite by the same argument; this is Baumslag's theorem.

## Step 4: torsion-free circularity (item 4)

- If `N` is not residually finite, neither is `G`, because residual
  finiteness passes to subgroups.
- If `N` is residually finite, `R(G) ⊆ C_G(N)`. The latter is a finite normal
  subgroup, so it is trivial when `G` has no nontrivial finite normal
  subgroup. Hence `R(G) = 1`.
- A torsion-free group has no nontrivial finite normal subgroup.

## Step 5: calibration checks

- **Infiniteness of `N` is needed.** For `N = 1` the conclusion of item 3
  would say that every hyperbolic group has finite residual, which is
  exactly the open infinite-residual shape of Gromov's question. Outside the
  hyperbolic class the step genuinely fails: for a perfect group `Q` with no
  nontrivial finite quotient and a perfect central extension `E` of `Q` by
  `C_p`, every finite image of `E` is abelian and perfect, so `R(E) = E`,
  while `N = C_p` is residually finite. No hyperbolic instance of this
  failure is known, and one would itself be a counterexample.
- **Normality is needed.** A counterexample `G` contains infinite
  residually finite subgroups, for example cyclic ones. These are not normal.
- **Consistency with the Leavitt cover.** In
  [[leavitt-kazhdan-cover-rf-iff-kernel-rf]] the cover is torsion-free with
  `C_G(N) = 1`, and item 4 recovers its residual-finiteness equivalence
  without using the Leavitt quotient.
