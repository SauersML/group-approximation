---
rg: 2
id: binary-self-similar-completions-over-free-bases-have-zero-kh
kind: claim
title: Every binary Leavitt–Nekrashevych or self-similar completion of a free algebra has vanishing homotopy K-theory, so for those finitely presented hosts the K-gate G3r is purely a nil-term question
distinct_from:
  noninjective-ln-completions-have-self-similar-bases: that proves finite presentation and identifies the base B/J; this computes the homotopy K-theory of the same rings.
---

**ESTABLISHED** (lane proof, not reviewed; no priority claimed). It rests on the import
`lescure-kh-exact-sequence-for-algebraic-cuntz-pimsner-rings` and on Gersten's theorem
`K_*(F<X>) ≅ K_*(F)` for regular noetherian `F` (K-theory of free rings, 1974; cited, not read
here).

## Statement

Let `K` be a field, `B = K<X>` free on a finite set, and `ψ : B -> M_2(B)` any unital
`K`-algebra homomorphism, injective or not. Then `KH_n(O_ψ(B)) = 0` for all `n ∈ Z`.

More generally, suppose `ψ : B -> M_d(B)` is unital and `B` is any unital `K`-algebra with
`KH_*(B) = KH_*(K)` through `K -> B`. Then `KH_n(O_ψ(B))` is the cofiber of multiplication by
`1 - d` on `KH_*(K)`. It vanishes iff `d = 2`, because `KH_0(K) = Z`.

## Proof

- **`KH` of the base.** Put `F = K[t_1..t_p]`, which is regular noetherian. Then
  `B[t_1..t_p] = F<X>`, so by Gersten `K_*(B[t_1..t_p]) = K_*(F) = K_*(K)`. So `B` is
  `K`-regular, and `KH_*(B) = K_*(B) = K_*(K)` through `K -> B`.
- **The map `1 - KH(ψ)`.** `ψ` is unital and `K`-linear, so `ψ(c) = c·1_2` for `c ∈ K`. The
  composite `K -> B -> M_2(B)` is therefore the sum of two orthogonal corner embeddings, and on
  `KH` it induces multiplication by `2` under Morita invariance, since `KH` is additive and
  `M`-stable. So `1 - KH_n(ψ) = -1`, an isomorphism.
- **Conclusion.** By the specialization in `lescure-kh-exact-sequence-for-algebraic-cuntz-pimsner-rings`,
  with `𝓘 = R = B`, exactness forces `KH_*(O_ψ(B)) = 0`.

The general case is the same computation, with `1 - d` in place of `-1`. `∎`

## Lesson for general BH

- **What the K-gate becomes.** For the finitely presented hosts of the self-similar algebra route
  (`algebra-bh-via-simple-self-similar-completions`, bh-algebra), homotopy K-theory vanishes with
  no hypothesis. The only possible obstruction to `K_1 = K_2 = 0`, i.e. gate G3r and gate A2 of
  Strategy 2, is the nil part `ker(K_n -> KH_n)`. For instance, gate G3r holds for `O_ψ(B)` if
  `O_ψ(B)` is `K_2`-regular.
- **Which recursions are safe.** For injective `ψ` with `B^2` flat as a left `B`-module, `O_ψ` is
  a universal localization of the tensor algebra `T_B(B^2)`. That is the Ara–Brustenga–Cortiñas
  shape, where the nil terms are twisted `NK` terms
  (`abc-leavitt-kh-vanishing-and-nil-splitting-citation`). For non-injective `ψ`, the left module
  has an annihilator (`J ≠ 0`), and no regularity argument applies.
- **Tension with the input.** So the recursions that can carry complex inputs (non-injective ones,
  which escape the complexity fence) are exactly those where the nil terms are uncontrolled.
- **Arity matters only for the bare host.** Only `d = 2` gives `KH(O_ψ) = 0`. For `d >= 3`, the
  cokernel `Z/(d-1)` of `1 - d` on `KH_0 = Z` survives. The group transfer uses
  `O_ψ ⊗ L_2`, and `KH(A ⊗ L_2) = 0` for every `A`
  (`abc-leavitt-kh-vanishing-and-nil-splitting-citation`). There the arity is irrelevant
  (bh-algebra).
- **Where the nil terms live.** `O_ψ(K<X>) ≅ O_ψ̄(B/J)` with `ψ̄` injective
  (`noninjective-ln-completions-have-self-similar-bases`). So the nil terms are those of the
  self-similar quotient `B/J`, not of the free base. For lossless monomial recursions, `B/J` is
  a monomial algebra, and the gate is twisted-nil vanishing over monomial algebras (bh-algebra).
