---
rg: 2
id: kazhdan-kernel-block-invariance-proof
kind: route
title: Blocks map to blocks, which gives a sofic representation of the quotient, which must be trivial
target: kazhdan-kernel-blocks-invariant-under-sofic-invisible-quotient
requires:
  - kun-expander-decomposition-formalized
artifacts:
  - research/artifacts/hyperbolic-leavitt-cover-relative-defect-2026-09-12.md
---

Full proof: artifact Section 7. Error terms are `o(|X_n|)` along `U`, summed
over blocks. "Most blocks" means all blocks outside a set of total size
`o(|X_n|)`.

1. **Images are almost invariant.** Fix `g`. For `s in S`, `g^-1 s g` is a
   word of bounded length in `S`, so `sigma(s) sigma(g) B ≈ sigma(g) B` for
   most blocks.
2. **Almost invariant sets are unions of blocks.** By the uniform Cheeger
   constant, an almost `S`-invariant set meets each block in almost none or
   almost all of it.
3. **One block.** `A = sigma(g)B` is an expander for the generating set
   `gSg^-1` of `N`, being isomorphic through `sigma(g)` to `B` with `S`. Each
   `A cap B'` is almost `S`-invariant, hence almost `gSg^-1`-invariant, because
   `gSg^-1` consists of bounded words in `S`. So a single block `B'` carries
   almost all of `A`, and `|B'| ≈ |B|`.
4. **A sofic representation of `Q`.**
   - Write `beta_g(B) = B'`. Then `beta_(gn) = beta_g` for `n in N`, and
     `beta_(gh) = beta_g beta_h` on most blocks.
   - Order each block and let `tau_n(gN)` map the `k`-th point of `B` to the
     `k`-th point of `beta_g(B)`.
   - Order-preserving maps compose, so `tau` is an asymptotic homomorphism of
     `Q`, that is, a homomorphism `Q -> S_U`.
5. **Triviality.** By hypothesis `tau` is trivial. A point of `B` is fixed only
   if `beta_g(B) = B`. So `sigma(g)B ≈ B` on most blocks.

The fixed-algebra form follows from Kun--Thom Lemma 2.3, which identifies
`D_U^(sigma(N))` with the block algebra. ∎
