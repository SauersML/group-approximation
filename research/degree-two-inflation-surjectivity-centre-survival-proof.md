---
rg: 2
id: degree-two-inflation-surjectivity-centre-survival-proof
kind: route
title: Reduce the extension mod n, inflate its class from a finite quotient, and map onto the finite extension through the pullback
target: degree-two-inflation-onto-makes-z-extension-centres-survive
requires: []
---

## Proof

Standard facts used (not re-read at source; Brown, *Cohomology of Groups*, IV.3): for a group `K`
and an abelian group `A` with trivial action, equivalence classes of central extensions
`1 → A → E → K → 1` correspond bijectively to `H^2(K;A)`; pushing an extension forward along a
homomorphism `A → A'` changes its class by the induced coefficient map; pulling back along
`θ : K' → K` changes it by `θ^*`.

1. **Reduction.** Let `c ∈ H^2(K;Z)` be the class of `K~`. The quotient `K~_n = K~/<z^n>` is the
   pushout of `K~` along `Z → Z/n`. So `1 → Z/n → K~_n → K → 1` is central with class `c̄`, the image
   of `c` in `H^2(K;Z/n)`, and `z` maps to a generator of `Z/n`.
2. **Inflation.** By (G2) there are a finite-index normal `N` with finite quotient
   `θ : K → Q = K/N` and `β ∈ H^2(Q;Z/n)` with `θ^*β = c̄`. Let `1 → Z/n → E → Q → 1` be a central
   extension with class `β`; `E` is finite.
3. **Pullback.** `P = {(k, e) ∈ K × E : θ(k) = π(e)}` is a central extension of `K` by `Z/n`, with
   `Z/n` embedded as `{(1, a)}`, and its class is `θ^*β = c̄`.
4. **Equivalence.** `K~_n` and `P` have the same class, so there is an isomorphism `f : K~_n → P`
   over `K` that is the identity on `Z/n`.
5. **The finite quotient.** The composite
   `K~ → K~_n --f--> P --pr_2--> E` is a homomorphism into the finite group `E`. It sends `z` to
   `pr_2(f(z̄)) = pr_2(1, generator) = ` a generator of `Z/n ⊂ E`, which has order exactly `n`.
   Replacing `E` by the image gives a finite quotient of `K~` in which `z` has order `n`.
6. **Serre goodness.** If inflation `H^2(K^;Z/n) → H^2(K;Z/n)` is onto, any class is the image of a
   continuous class of `K^`, which factors through one finite quotient `K^/U = K/(U ∩ K)` because
   continuous cohomology with finite trivial coefficients is the colimit over open normal
   subgroups; composing inflations gives (G2).
7. **Kazhdan consequence.** `H^2(K;Z) → Hom(H_2(K;Z), Z)` is onto (universal coefficients) and the
   target has rank `b_2(K;Q) >= 1`, so some `c` is nonzero on `H_2(K;Z)`. In the five-term sequence
   `H_2(K) → Z → H_1(K~_c) → H_1(K) → 0` the connecting map is evaluation of `c`, with image `mZ`,
   `m != 0`; `H_1(K)` is finite because `K` is Kazhdan. So `H_1(K~_c)` is finite. ∎
