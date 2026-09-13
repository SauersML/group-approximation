---
rg: 2
id: liftable-masa-iff-uniform-hs-kun-partitions-proof
kind: route
title: Diagonalize partition levels along the ultrafilter, and build a counterexample model from a failing sequence of approximate models
target: liftable-masa-in-every-model-iff-uniform-hs-kun-partitions
requires: [hs-block-gap-iff-liftable-masa-of-actor-commutant]
artifacts:
  - research/artifacts/hs-masa-lift-positive-2026-09-13.md
---

Full derivation: `research/artifacts/hs-masa-lift-positive-2026-09-13.md`, Sections 2 and 3.
Below, BG1-BG4 are items 1-4 of `hs-block-gap-iff-liftable-masa-of-actor-commutant`.

1. **One model, masa => partitions.** BG1 gives vanishing boundary. BG3 gives `gamma(P_k, kappa) -> 0`,
   where BG3 uses property (T) of `G` on `L^2(M)`.
2. **One model, partitions => masa.** Suppose that for each `j`, `U`-most `k` admit a partition at
   level `2^-j` with some fixed `k' > 0`.
   - Take the largest `j(k) <= k` with `k` in the first `j(k)` level sets, so `j(k) -> infinity` along `U`.
   - The chosen partitions have `b -> 0` and `gamma(., k') -> 0`.
   - BG1 and BG4 make `prod_U C_k` a masa.
3. **Block algebra form.** `Z(prod_U D(P_k)) = prod_U C(P_k)`, by Haar averaging over `U(D(P_k))` and
   a maximizing choice of unitaries. With BG2, `C' cap M = D`, so `Q cap C' = sigma(G)' cap D`.
4. **Uniform form, (3) => (1).** For fixed `(eps, R)`, the lifts of a model are `(eps, R)`-models on
   `U`-most coordinates, because `sigma` is a homomorphism and the ball is finite. Apply step 2.
5. **Uniform form, (1) => (2).** If `DEC_kappa` fails at `beta`, pick `(1/k, k)`-models `u^(k)` with no
   good partition, and extend them by `1`. The classes `[(u^(k)_g)_k]` define a homomorphism of `G`.
   Item (1) and step 1 give good partitions on a `U`-large set, which is a contradiction.
6. **One-level decomposition => (1).** Adjoin the removed corner `q_0` as one block. It costs boundary
   `2 tau(q_0)` and slack `k'^2 tau(q_0)`. Weighted summation of the per-block inequalities gives
   step 2's hypothesis.
7. **Arithmetic.** A partition of `M_n` has at most `n` members, and `gamma <= beta` quantifies over
   contractions. So for rational parameters the inner statement is first-order over the reals.
