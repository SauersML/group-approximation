---
rg: 2
id: sft-crossed-product-stable-k2-is-finitely-generated
kind: claim
title: The stable K_2 of a finitely presented free minimal Z^2-SFT crossed product over F_q is finitely generated
distinct_from:
  binary-cantor-ring-stable-steinberg-group-centrally-closed: that computes K_2 = 0 for d = 1 over F_2; this is d = 2, where K_2 is nonzero (z2-crossed-product-steinberg-kernel-is-nonzero) and only finite generation is asked.
  leavitt-tensor-steinberg-kernel-is-stable-k2: that is finite generation of K_2 over Leavitt tensor hosts, where the unstable kernel is already identified with K_2; this is the stable computation for a tracial Z^2 crossed product, with no stability statement.
  rigid-sft-elementary-group-mod-centre-is-fp: that is finite normal generation of the unstable kernel; this is the stable half only, and does not imply it without injective stability.
---

**OPEN.** Let `Ω` be a free minimal `Z^2`-SFT such that `R = LC(Ω, F_q) ⋊ Z^2` is finitely
presented. Then `K_2(R)` is a finitely generated abelian group.

## Attempts

- **It is nonzero.** `z2-crossed-product-steinberg-kernel-is-nonzero` gives a class of order divisible
  by `p`, or infinite, detected by a Hochschild cocycle. That is the symbol-type class `[h_12(u_1), h_13(u_2)]`.
- **Iterated twisted Bass--Heller--Swan (unverified).**
  - Write `R = B[t_2^(±1); sigma_2]` with `B = A[t_1^(±1); sigma_1]` and `A = LC(Ω, F_q)`.
    `abc-twisted-laurent-k-theory-fibration` (ABC Theorem 3.6) applies to any unital ring.
  - For `A`: `K_0(A) = C(Ω,Z)`, `K_1(A) = C(Ω, F_q^x)` and `K_2(A) = 0`, and the Nil terms vanish
    because `A` is regular supercoherent (ABC Lemma 7.2).
  - Over `F_2`, where `K_1(A) = K_2(A) = 0`, the long exact sequence for `B` gives
    `K_1(B) ≅ ker(1 - sigma_1 on K_0(A)) = C(Ω,Z)^(sigma_1)` and `K_2(B) = 0`.
  - At the second step Theorem 3.6 gives `K_2(R)` as the direct sum of the twisted Nil groups
    `NK_2(B; sigma_2)_(±)` and an extension of `ker(1 - sigma_2 on K_1(B))` by
    `coker(1 - sigma_2 on K_2(B)) = 0`. If those Nil groups vanish, the first group is
    `C(Ω,Z)^(Z^2) = Z` (minimality), and `K_2(R) ≅ Z`.
  - **Where it dies.** `B = LC(Ω, F_q) ⋊ Z` is not commutative, and regular supercoherence of `B` is not
    known here, so ABC Lemma 7.2 does not apply at the second step.
- **Over `F_q` with `q > 2` (unverified).**
  - An extra extension term `H_1(Z^2; C(Ω, F_q^x))` appears. It has exponent `q - 1`, so it is
    finitely generated iff it is finite.
  - By Poincaré duality for `Z^2` it is `H^1(Z^2; C(Ω, Z/(q-1)))`, a first tiling cohomology with
    finite coefficients.
  - **Where it dies.** Finiteness of that group for a general free minimal `Z^2`-SFT is not known
    here, and no example is checked.
- **Hochschild invariants give no obstruction.** Heuristically, every functional built like the one
  in `z2-crossed-product-steinberg-kernel-is-nonzero` factors through `H_2(Z^2; A) ≅ A^(Z^2) = F_q`.
  So such functionals see at most a finite quotient.
