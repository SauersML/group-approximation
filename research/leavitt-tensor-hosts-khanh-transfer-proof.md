---
rg: 2
id: leavitt-tensor-hosts-khanh-transfer-proof
kind: route
title: Rerun Khanh's criteria over B ⊗ L, normalizing Leavitt reduction by simplicity of B
target: leavitt-tensor-hosts-acyclic-steinberg-and-fp
requires:
  - leavitt-unit-group-finitely-presented
  - leavitt-steinberg-map-iso-from-rank-three
artifacts:
  - research/artifacts/boone-higman-leavitt-tensor-hosts-2026-09-12.md
---

The two prerequisites are the verified Khanh imports. The general criteria
used below come from the same verified source: Theorems 2.2 and 5.1, Lemmas
2.3, 2.4 and 5.2, and the GE, Voronetsky and Krstić--McCool steps. Put
`R = B ⊗ L` with `B` simple.

1. **Normalization (artifact Lemma 2.1).** Khanh's Lemma 4.1 argument with
   coefficients in `B` gives `x` and words `η_i` with `η_i* a_i x = c_i ⊗ 1`,
   `c_i != 0`.
2. **Division (Lemma 2.2).** Use `Σ_k y_(ik) c_i z_(ik) = 1` in `B`, and
   distinct words `β_(ik)` of one length. Put `Z = Σ z_(ik) ⊗ β_(ik)`,
   `Y_i = Σ_k y_(ik) ⊗ β_(ik)*`, `u_i = Y_i η_i*` and `X = xZ`. Then
   `u_i a_i X = 1`, and `ker u_i ≅ ker Y_i ⊕ R^(|η_i|) ≅ R` because
   `R ⊕ ker Y_i ≅ R`.
3. **Frames (Proposition 2.4, Corollary 2.5).** Khanh's Proposition 4.2 with
   `(X, u_i)` gives the highly connected frame complexes `X_r(R)` and a simply
   connected `|X_4(R)|`.
4. **Standard inclusions (Proposition 3.1).** The compression
   `c(u) = e u e* + f f*` and the unit `w` with `w c(u) w^-1 = c(c(u))` make
   `c_*` idempotent. When `H_n(GL_∞(R)) = 0`, `c_*` is locally nilpotent, hence
   zero on `H_n`. The plus construction turns `K_i(R) = 0` for `i <= N` into
   this hypothesis for `n <= N`.
5. **Acyclicity (Theorem 4.1).** Khanh's Theorem 2.2 induction uses hypothesis
   (1) only in degree `n` and hypothesis (2) only at `r = n+3`.
6. **Steinberg and finite presentation (Theorem 4.2).**
   - GE and perfectness give `GL_m = E_m`.
   - `H_2(GL_3) = 0`, Lemma 5.2, step 3 and Theorem 5.1 give `φ_4` iso, and
     Voronetsky gives every `r >= 3`.
   - `R` is finitely presented as a ring when `B` is (generators of `B`,
     `e, f, s, t`, and the commutators), so Krstić--McCool presents
     `St_5(R) ≅ R^x`.
