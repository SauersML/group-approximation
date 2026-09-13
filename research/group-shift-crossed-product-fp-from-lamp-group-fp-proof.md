---
rg: 2
id: group-shift-crossed-product-fp-from-lamp-group-fp-proof
kind: route
title: Fourier transform on the dual compact group and presentations of group algebras
target: group-shift-crossed-product-fp-from-lamp-group-fp
requires: [sft-crossed-product-fp-iff-quantum-rigid]
artifacts:
  - research/artifacts/quantum-rigidity-group-shifts-and-gluing-2026-09-13.md
---

The artifact, Section 1 (Proposition G2), gives the proof.

1. **Characters.** `X = Hom(M, F_p)` is a compact totally disconnected group, and its continuous characters
   into `μ_p ⊆ k^×` are the elements of `M`.
   - Locally constant functions are finite combinations of characters of finite quotients.
   - Since `p` is invertible in `k` and `μ_p ⊆ k`, the characters span `LC(X, k)` and are linearly
     independent. So `LC(X, k) ≅ k[M]`.
2. **Crossed product.** The shift acts on characters by the module action. Hence
   `LC(X, k) ⋊ Z^2 ≅ k[M] ⋊ Z^2 = k[M ⋊ Z^2]`.
3. **Presentations.** A finite group presentation `<S | R>` gives the algebra presentation with generators
   `s, s^(-1)` (`s ∈ S`), the relations `s s^(-1) = s^(-1) s = 1`, and `r = 1` (`r ∈ R`).
4. **Rigidity.** A finitely presented crossed product is `D`-quantum rigid for some `D`, by the cited claim.
