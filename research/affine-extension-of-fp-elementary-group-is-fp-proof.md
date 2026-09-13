---
rg: 2
id: affine-extension-of-fp-elementary-group-is-fp-proof
kind: route
title: Rebuild the translations as commutators of elementary generators with the unit translations
target: affine-extension-of-fp-elementary-group-is-fp
requires: []
artifacts:
  - research/artifacts/bh-sl3-zt-host-2026-09-12.md
---

Full details are in §2 of the artifact. Let `P` be the presentation in the claim
and `π : P -> G = R^n x| E_n(R)` the natural map; the relations hold in `G`.
- By (E), `e_ij(ε) -> x_ij(ε)` extends to a homomorphism `φ : E_n(R) -> P`. Write
  `x_ij(r) = φ(e_ij(r))`; all Steinberg relations hold among them.
- The `e_ij(ε)` generate `E_n(R)`, because `[e_il(μ), e_lj(ε)] = e_ij(με)`.
- The identities used are `[AB,C] = A[B,C]A^-1[A,C]` and `[a,bc] = [a,b]·b[a,c]b^-1`.

**A. `[x_ij(r), τ_k] = 1` for all `r` and all `k != j`.**
- For a monomial, induct on degree with `x_ij(με) = [x_il(μ), x_lj(ε)]`,
  `l ∉ {i,j,k}`, together with (C1).
- For a sum, use additivity.

Put `y^k_i(r) = [x_ik(r), τ_k]` for `k != i`.

**B. `y^k_i(r)` commutes with every `τ_l`.**
- **Case `l != k`.** Use A and (C3).
- **Case `l = k`.** Let `Y = x_ik(r) τ_k x_ik(r)^-1`, pick `l ∉ {i,k}` and let
  `h = x_kl(1)`.
  - `h` fixes `τ_k` by (C1).
  - `h` fixes `Y`, since `h x_ik(r) h^-1 = x_il(-r) x_ik(r)` and `x_il(-r)`
    commutes with `x_ik(r)` and with `τ_k`.
  - `h τ_l h^-1 = τ_l τ_k` by (C2).
  - Conjugating `[τ_l, Y] = 1` by `h` gives `[τ_l τ_k, Y] = 1`, so `[τ_k, Y] = 1`.

**F1. `y^k_i(r) = y^(k')_i(-r)^-1` for distinct `i, k, k'`.**
- Conjugate `[x_ik(r), τ_k'] = 1` by `u = x_kk'(1)`. This uses
  `u x_ik(r) u^-1 = x_ik'(-r) x_ik(r)` and `u τ_k' u^-1 = τ_k' τ_k`.
- Expand with A and B.
- Applying F1 twice through `k' ∉ {i,k,k''}` shows that `y_i(r) := y^k_i(r)` does
  not depend on `k`.

**F2. `y_i(r+s) = y_i(s) y_i(r)` and `y_i(1) = τ_i`.**
- Expand `[x_ik(r)x_ik(s), τ_k]`.
- Represent `y_i(s)` with `k' ∉ {i,k}`, where it commutes with `x_ik(r)`.
- (C2) and (C3) give `y_i(1) = τ_i`.

**F3. `y_i(r)` and `y_j(s)` commute.** Take `k ∉ {i,j}` for `y_i` and
`k' ∉ {i,j,k}` for `y_j`, then use B, the Steinberg relations and A.

**F4. Conjugation by `x_ab(r')`.**
- **If `b != i`,** `x_ab(r')` fixes `y_i(r)`: take `k ∉ {i,a,b}`.
- **If `b = i`,** `x_ab(r') y_i(r) x_ab(r')^-1 = y_i(r) y_a(r'r)`: take `k ∉ {i,a}`,
  use `x_ai(r') x_ik(r) x_ai(r')^-1 = x_ak(r'r) x_ik(r)`, and represent `y_i(r)`
  with `k' ∉ {i,a,k}`.

**Conclusion.**
1. `z(v) = ∏ y_i(v_i)` is a homomorphism `R^n -> P` with `π∘z = id`. So its image
   `N` maps isomorphically onto `R^n`.
2. `N` contains the `τ_i` and is normalized by all the generators (B, F4), so it
   is normal.
3. `φ` induces a surjection `E_n(R) -> P/N`. Its composite with
   `P/N -> G/R^n = E_n(R)` is the identity, so `P/N -> G/R^n` is an isomorphism.
4. Hence `π` is an isomorphism, and `G` is finitely presented. ∎
