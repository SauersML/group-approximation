---
rg: 2
id: tate-diagonal-cone-is-weakly-contractible-wreath-object
kind: claim
title: The crossed product of the cone of the Tate diagonal of C*_r(Γ) is the reduced crossed product by Γ ≀ Z/p of one weakly contractible object, contractible on Γ^p
distinct_from:
  kazhdan-group-algebra-tate-diagonal-is-kkg-equivalence: that is the open question whether the Tate diagonal is a KK^G-equivalence; this proves an exact reformulation of it as the vanishing of W ⋉_r Y for one explicit weakly contractible W-algebra Y, and makes its K-invisibility rigorous.
  hyperbolic-bcc-finite-wreath-products: that is Baum–Connes with coefficients for finite wreath products; this uses it only through Meyer–Nest's obstruction functor.
---

**ESTABLISHED (derivation; unreviewed).**
- **Setting.** `p` is prime, `G = Z/p = <σ>`, and `Γ` is a torsion-free countable group.
  - `W = Γ ≀ G = Γ^p ⋊ G`, with `q : W → G`, and `H = ΔΓ × <σ>`.
  - `ε = [ℓ²(W/H)] ∈ KK^W(C_0(W/H), C)`.
  - `1_T` is the Tate object, and `Y := cone(ε) ⊗ q^*(1_T)`.
  - `T(Δ) = 1_T ⊗ Δ` is the Tate diagonal `1_T ⊗ τ(C*_r Γ) → 1_T ⊗ C*_r(Γ^p)`.
- **Group theory.** Every nontrivial finite subgroup of `W` is conjugate to `<σ>`, and
  `N_W(<σ>) = C_W(σ) = H`. The only fixed point of `w<σ>w^(−1)` on `W/H` is `wH`.

1. `Res^W_F Y ≃ 0` for every finite `F ≤ W`, so `Y` is weakly contractible in the sense of Meyer–Nest.
   Moreover `Res^W_(Γ^p) Y ≃ 0`.
2. `W ⋉_r Y ≅ cone(T(Δ) ⋊ G)`, compatibly with the dual `Ĝ`-actions.
3. `T(Δ) ⋊ G` is a KK-equivalence iff `W ⋉_r Y ≃_KK 0`. `T(Δ)` is a `KK^G`-equivalence iff
   `W ⋉_r Y ≃ 0` in `KK^Ĝ`.
4. If `W` satisfies Baum–Connes with coefficients, then `K_*(W ⋉_r (Y ⊗ B)) = 0` for every separable
   `W`-algebra `B`.
5. If `Γ` is a-T-menable, then `Y ≅ 0` in `KK^W`, and `T(Δ)` is a `KK^G`-equivalence.

**Consequences.**
- By `hyperbolic-bcc-finite-wreath-products`, item 4 applies to every torsion-free hyperbolic `Γ`,
  including torsion-free uniform lattices in `Sp(n,1)`. This replaces the unchecked cellular
  localization sketch in `research/artifacts/uct-kk-norm-functor-2026-09-13-part3.md` §11(c).
- If `W` has a γ-element, then `Y = (1 − γ_W)Y`. The "map between `(1 − γ)`-parts" of that
  artifact is exactly the crossed product of the single object `Y`.

Proof: `tate-diagonal-cone-is-weakly-contractible-wreath-object-proof`.
