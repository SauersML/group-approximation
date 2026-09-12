---
rg: 2
id: aut-out-free-abelianized-extension-proof
kind: route
title: The Fox Jacobian determinant restricts to n minus one times abelianization on inner automorphisms
target: aut-out-free-abelianized-extension-splits-rationally
requires: []
artifacts:
  - research/artifacts/bh-aut-out-virtual-section-2026-09-12.md
---

Full computation: Section 1 of the artifact.

1. **The determinant is a crossed homomorphism.**
   - Put `M(φ)_{ki} = ∂φ(x_k)/∂x_i`. The Fox chain rule gives
     `M̄(φψ) = φ_*(M̄(ψ))·M̄(φ)` over `Z[H]`.
   - Taking determinants, and using that the units of `Z[H]` are `±H`, gives
     `h(φψ) = h(φ) + φ_* h(ψ)`.
2. **Its value on inner automorphisms.** For `φ = ι_g` with `t = [g]`, the
   abelianized Jacobian is `t·I + u v^T` with `u_k = 1 − t_k` and
   `v_i = ∂̄_i g`. The fundamental formula gives `v^T u = 1 − t`, so the
   determinant is `t^{n−1}` and `h(ι_g) = (n − 1)[g]`.
3. **The extension class is torsion.**
   - `Inn(F_n) ≅ F_n`, and `[F_n, F_n]` is characteristic.
   - `h|_Inn` is a homomorphism, so `h` descends to `E = Aut(F_n)/[Inn, Inn]`
     with `h|_H = (n − 1)·id`.
   - Hence `(n − 1)·c = 0`.
4. **π^* is injective.** In the two-row Lyndon--Hochschild--Serre spectral
   sequence for `1 → F_n → Aut(F_n) → Out(F_n) → 1`, with `M` pulled back from
   `Out(F_n)`, the kernel of `π^*` is the image of `d_2`.
   - `d_2` agrees with the `d_2` of the abelianized extension, because the
     `E_2` rows 0 and 1 map isomorphically.
   - For an abelian kernel, `d_2` is cup product with `c` followed by
     evaluation. This is the standard Hochschild--Serre description, cited and
     not re-read.
   - `c ⊗ Q = 0`, so `d_2 = 0` and `π^*` is injective.
