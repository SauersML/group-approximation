---
rg: 2
id: minimal-cantor-crossed-product-k-theory-formula-proof
kind: route
title: Algebraic Pimsner–Voiculescu over LC(X,F_q), coefficients LC(X,K_n(F_q)), invariants are constants by minimality, coinvariants are K^0 ⊗ M, and Quillen's parity vanishing removes every extension problem
target: minimal-cantor-crossed-product-k-theory-formula
requires:
  - abc-twisted-laurent-k-theory-fibration
  - quillen-k-theory-of-finite-fields
artifacts:
  - research/artifacts/sk-open-4-dictionary-2026-09-13-part1.md
---

Put `A = LC(X,F_q)` and `σ(f) = f∘T^(−1)`, so `R_X = A[t,t^(−1);σ]`.

- **Step 1 (A is regular supercoherent).** This is word for word Steps 1–2 of `subshift-crossed-product-k0-is-coinvariant-group-proof`.
  - `A` is the directed union of `A_P ≅ F_q^P` over finite clopen partitions `P`.
  - Each `A_P[t_1..t_p]` is regular Noetherian, and the transition maps are flat.
  - A finitely presented module over the colimit comes from a finite stage. It keeps its finite projective resolution, and kernels stay finitely presented.
- **Step 2 (fibration).** `σ` is a unital automorphism. ABC Theorem 3.6 with `A = Z`, plus Lemma 7.2 (`abc-twisted-laurent-k-theory-fibration`), give the long exact sequence `… → K_n(A) →(1−σ_*) K_n(A) → K_n(R_X) → K_(n−1)(A) →(1−σ_*) K_(n−1)(A) → …`. So
  `0 → coker(1−σ_* | K_n(A)) → K_n(R_X) → ker(1−σ_* | K_(n−1)(A)) → 0`.
- **Step 3 (coefficients).**
  - K-theory preserves filtered colimits (quoted in the ABC node), so `K_n(A) = colim_P K_n(F_q)^P = LC(X, K_n(F_q))`.
  - `σ_*` acts by composition with `T^(−1)`, by naturality under the ring maps `A_P → A_(TP)`.
- **Step 4 (invariants, coinvariants).** For a discrete abelian group `M`:
  - An invariant locally constant `f: X → M` is constant on each dense orbit, hence constant, so `ker(1−σ_* | LC(X,M)) = M`.
  - `LC(X,M) = colim_P (Z^P ⊗ M) = C(X,Z) ⊗ M`, and `⊗M` is right exact, so `coker(1−σ_* | LC(X,M)) = K^0(X,T) ⊗ M`.
  - The images of `1 − σ_*` and `1 − T_*` coincide (Step 5 of the K_0 route).
- **Step 5 (assembly with Quillen).** `quillen-k-theory-of-finite-fields` gives `K_(2i)(F_q) = 0` and `K_(2i−1)(F_q) = Z/(q^i−1)`.
  - `n = 2i ≥ 2`: the cokernel term vanishes, so `K_(2i)(R_X) ≅ Z/(q^i−1)`.
  - `n = 2i+1 ≥ 3`: the kernel term `K_(2i)(F_q)` vanishes, so `K_(2i+1)(R_X) ≅ K^0 ⊗ Z/(q^(i+1)−1)`.
  - `n = 1`: `0 → K^0 ⊗ F_q^× → K_1(R_X) → Z → 0` splits because `Z` is free. ∎

**Model tests.**
- One-point system: Bass–Heller–Swan `K_n(F_q[t^(±1)]) = K_n(F_q) ⊕ K_(n−1)(F_q)` ✓.
- Periodic orbit of length `p`: `R ≅ M_p(F_q[t^(±1)])` and `K^0 = Z`, which agrees with Morita invariance ✓.
- Sturmian `X_α` over `F_2`: `K_3 ≅ (Z/3)²`.
