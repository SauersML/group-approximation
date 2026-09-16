---
rg: 2
id: toeplitz-pair-algebra-is-qd-with-non-qd-irreps-proof
kind: route
title: Matrix units give K plus K, the symbol pullback gives type I, and the bilateral shift gives quasidiagonality
target: toeplitz-pair-algebra-is-qd-with-non-qd-irreps
requires: []
artifacts:
  - research/artifacts/bk-type-i-k0-embedding-equivalence-2026-09-16.md
---

Full proof: artifact §5, steps 1--6.  Put `V = S ⊕ S*` and `e_0 = 1 − SS*`.

1. **Compacts.**
   - `V*V − VV* = e_0 ⊕ (−e_0)`, whose square is `e_0 ⊕ e_0`.
   - `Se_0 ⊕ 0 = V(e_0 ⊕ e_0)` gives `e_0 ⊕ 0`, and hence `0 ⊕ e_0`.
   - `V^k(e_0 ⊕ 0)V^{*l}` and `V^{*k}(0 ⊕ e_0)V^l` are all the matrix units of
     `K ⊕ 0` and `0 ⊕ K`.
2. **Pullback.**
   - `T'` lies in the pullback `P`, and `T' → C(T)`, `(a, b) ↦ q(a)`, is onto.
   - An element of `P` minus a lift in `T'` has zero symbols, so it lies in
     `K ⊕ K ⊆ T'`.  Hence `T' = P`.
   - An extension of a commutative algebra by `K ⊕ K` is type I (standard).
3. **Quasidiagonality.**
   - Relabel `ξ_n ⊕ 0 ↦ f_n` and `0 ⊕ ξ_n ↦ f_{−n−1}`.  Then
     `V = W − f_0 ⊗ f_{−1}*`, with `W` the bilateral shift.
   - `W` is normal, so `W = D + compact` with `D` diagonal (Weyl--von
     Neumann--Berg; I. D. Berg, Trans. AMS 160 (1971), not re-checked).
   - The projections onto the first `n` basis vectors of `D` commute with `D`
     and asymptotically with compacts.  So `||[P_n, V]|| → 0`.
   - By the derivation property and density, `||[P_n, x]|| → 0` for all
     `x ∈ T'`.
4. **Irreducibles.**
   - An irreducible representation not vanishing on the ideal `K ⊕ K` extends
     an irreducible representation of `K ⊕ K`, so it is `π_1` or `π_2`.  All
     others are characters.
   - `e_0 ⊕ 0` is annihilated by `π_2` and by the characters, so a faithful
     family contains `π_1`.  Symmetrically it contains `π_2`.
5. **Images.**
   - `π_1(T') = T` contains a non-unitary isometry, so it is not finite and not
     quasidiagonal.
   - `a ↦ ∫ q(a)` is a tracial state on `T`.
   - `ker π_1 = 0 ⊕ K`.
6. **Boundary.**  The lift `V` of `z` has Fredholm components of index `−1` and
   `+1`.
