---
rg: 2
id: bernoulli-bc-splits-into-host-and-cylinder-comparison-proof
kind: route
title: Split off the fixed point, apply the Bernoulli weak K-equivalence and going-down, and filter by support size
target: bernoulli-bc-splits-into-host-and-cylinder-comparison
requires:
  - bernoulli-shift-weak-k-equivalence-and-going-down
  - amenable-kernel-bc-transfer-and-ktop-half-exactness
  - split-quotients-give-exact-reduced-crossed-products
  - lueck-surjective-assembly-traces-lie-in-lambda-g
  - module-dual-actions-have-no-wandering-open-sets
artifacts: [research/artifacts/bc-bernoulli-cylinder-comparison-2026-09-13.md]
---

Full proofs are in Section 2 of the artifact. Outline:

- **Lemma E.** Let `0 -> I -> A -> B -> 0` be exact and suppose `B ⋊_max G = B ⋊_r G`. Then the reduced sequence is
  exact. Proof: a kernel element lifts to `A ⋊_max G`, dies in `B ⋊_max G`, so lies in `I ⋊_max G`, whose image in
  `A ⋊_r G` is `I ⋊_r G`. This covers `B = c_0(Y)` for discrete `Y` with finite stabilizers, by Green imprimitivity.
- **Item 1.**
  - Evaluation at the fixed configuration `0` is split by the unit, so `C(X) ≅ I_1 ⊕ C` in `KK^G`.
  - Both sides of assembly are additive, and the reduced split sequence is exact by part (A) of
    `split-quotients-give-exact-reduced-crossed-products`.
- **Item 2.**
  - Item 1 of `bernoulli-shift-weak-k-equivalence-and-going-down` gives a weak K-equivalence
    `Φ : C ⊕ c_0(S) -> C(X)` whose `∅`-component is the unit. Put `T = r ∘ Φ ∘ incl`.
  - For each finite `H`, `K_*(Φ ⋊ H)` has block matrix `[[id, c], [0, K_*(T ⋊ H)]]`. It is invertible, so `T` is a weak
    K-equivalence.
  - Item 2 (going-down) makes `K^top_*(G; T)` bijective.
  - `c_0(S)` is a proper `G`-algebra, so item 3 makes `mu_(G, c_0(S))` bijective.
- **Item 3.** Descent is functorial for Kasparov products, which gives
  `mu_(G, I_1) ∘ K^top_*(G; T) = T_r ∘ mu_(G, c_0(S))` with both left factors bijective.
- **Item 4.**
  - Over a torsion-free group a weak K-equivalence only has to be a K-theory isomorphism.
  - The *-homomorphism `delta_s ↦ e_(ss) ⊗ 1_(C_s)` into `K(l^2 S) ⊗ I_1` is one: the cylinder functions `1_(C_s)` form
    a `Z`-basis of `C_c(X \ {0}, Z) = K_0(I_1)`, by inclusion-exclusion over `Z^Λ = Z1 ⊕ ⊕_(j>=1) Z1_(x_z=j)`.
  - Free orbits give `K_0(c_0(S) ⋊_r G) = ⊕_([s]) Z` and `K_1 = 0`.
- **Item 5.**
  - The same *-homomorphism maps `c_0(S_(>=k))` into `K ⊗ I_k`. On the quotients `c_0(S_k)` and
    `I_k/I_(k+1) = C_0({|supp x| = k}) ≅ c_0(S_k)` it is a corner embedding.
  - Lemma E makes both reduced sequences exact. The five lemma steps from `k` to `k+1`.
- **Item 6.** Item 2 of `amenable-kernel-bc-transfer-and-ktop-half-exactness` identifies assembly for `F_p wr_Z G` with
  `mu_(G, C(X))`, each half separately. Combine with items 1 and 3.
- **Item 7.**
  - Finite subgroups of `F_p wr_Z G` lie in `⊕_Z F_p`, so `Λ = Z[1/p]` and
    `lueck-surjective-assembly-traces-lie-in-lambda-g` applies.
  - The trace is Haar measure composed with the conditional expectation
    (`module-dual-actions-have-no-wandering-open-sets`, item 2), so a cylinder over `F` has trace `p^(-|F|)`.

**Context, not re-read:** functoriality of descent (Kasparov 1988), exactness of maximal crossed products, Green
imprimitivity, the Green--Julg identification `KK^H(C, D) = K_*(D ⋊ H)`. QED.
