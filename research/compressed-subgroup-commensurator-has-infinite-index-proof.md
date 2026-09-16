---
rg: 2
id: compressed-subgroup-commensurator-has-infinite-index-proof
kind: route
title: The relative index is a homomorphism on the commensurator, a finite-index compressor makes it onto Z, and property (T) forbids that
target: compressed-subgroup-commensurator-has-infinite-index
requires: []
artifacts:
  - research/artifacts/compressed-subgroup-commensurator-2026-09-16.md
---

This is a complete proof. Artifact Sections 0-2 carry every step in detail. The
skeleton is below. All groups are discrete.

**1. Relative index (artifact Lemma 1.1).**

- `A ~ B` means `[A : A cap B]` and `[B : A cap B]` are finite. For such pairs put
  `rho(A,B) = [A : A cap B] / [B : A cap B]`.
- For `D <= A cap B` of finite index in `A cap B`, the tower law gives
  `rho(A,B) = [A:D] / [B:D]`.
- If `A ~ B ~ C`, then `D = A cap B cap C` has finite index in `A cap B`, `B cap C` and
  `A cap C`, because `[A cap B : D] <= [B : B cap C]` via
  `x D |-> x (B cap C)`. So `~` is transitive, and
  `rho(A,C) = rho(A,B) rho(B,C)`.
- Conjugation preserves `~` and `rho`.

**2. Modular homomorphism (Lemmas 1.2, 1.3).**

- `Comm_G(Gamma) = { g : g Gamma g^-1 ~ Gamma }` is a subgroup, by conjugation and
  transitivity.
- `Delta(g) = rho(Gamma, g Gamma g^-1)` is a homomorphism. Take `A = Gamma`,
  `B = g Gamma g^-1`, `C = gh Gamma h^-1 g^-1`, and use `rho(B, C) = rho(Gamma, h Gamma h^-1)`.
- For `g in P_Gamma` we have `Gamma cap g Gamma g^-1 = g Gamma g^-1`. So `g` is in the
  commensurator exactly when `[Gamma : g Gamma g^-1]` is finite, and then `Delta(g)` is
  that index. It is at least 2 when `g` is strict.

**3. Finite-index compression gives a map onto `Z` (Proposition 2.1).**

- Let `t` be a strict compressor with `m = [Gamma : t Gamma t^-1]` finite, and `p` a
  prime dividing `m`.
- Then `v_p o Delta` is a homomorphism `Comm_G(Gamma) -> Z` taking the value
  `v_p(m) >= 1` at `t`. Divided by the generator of its image, it maps onto `Z`.
- Suppose instead only that `[G : Comm_G(Gamma)] = n` is finite.
  - Two of the cosets `t^i Comm_G(Gamma)`, `0 <= i <= n`, coincide. So `t^e` lies in
    `Comm_G(Gamma)` for some `e >= 1`.
  - `t^e` is again a strict compressor. If `t^k Gamma t^-k = Gamma`, the chain
    `Gamma >= t Gamma t^-1 >= ... >= t^k Gamma t^-k` collapses, forcing
    `t Gamma t^-1 = Gamma`.
  - So `t^e` has finite index, and the first bullet applies to `t^e`.

**4. The statements.**

- *Statement 1.* If `[G : Comm_G(Gamma)]` were finite, step 3 would give a surjection
  onto `Z` from a finite-index subgroup.
- *Statement 2.*
  - A strict compressor `t` exists. Otherwise `P_Gamma <= N_G(Gamma)`, and `Gamma` would
    be normal.
  - If every compressor had finite index, then `P_Gamma <= Comm_G(Gamma)` by step 2. So
    `Comm_G(Gamma) = G`, and step 3 applied to `t` gives `G -> Z` onto.
  - *Generation.* Let `S = P_Gamma \ Comm_G(Gamma)`, fix `p in S`, and let
    `q in P_Gamma cap Comm_G(Gamma)`.
    - `pq` is in `P_Gamma`, and it is not in `Comm_G(Gamma)`: otherwise `p = (pq) q^-1`
      would be.
    - So `q = p^-1 (pq) in <S>`, hence `P_Gamma <= <S>` and `<S> = G`.
    - By step 2, `S` is exactly the set of compressors of infinite index.
- *Statement 3.* Let `[G:H]` be finite.
  - Counting measure on `G/H` is a finite invariant measure. So `H` has (T) by
    Bekka--de la Harpe--Valette, *Kazhdan's Property (T)* (preprint dated February 23,
    2007), Theorem 1.7.1, transcribed in the artifact.
  - By Corollary 1.3.6 of the same text, `H/[H,H]` is finite. So every homomorphism
    `H -> Z` has finite image, hence is 0. (The same text records this combination as
    Corollary 1.7.2: a finite-index subgroup of a discrete Kazhdan group has finite
    abelianization.)
  - Artifact Remark 2.3 checks `Hom(H,Z) = 0` directly from the definition of (T): if
    `psi` is onto `Z`, the unit vectors `k^(-1/2) 1_{0..k-1}` in `l^2(Z)` are almost
    invariant, and there is no invariant vector.  ∎
