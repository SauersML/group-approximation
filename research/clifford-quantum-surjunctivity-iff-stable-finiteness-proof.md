---
rg: 2
id: clifford-quantum-surjunctivity-iff-stable-finiteness-proof
kind: route
title: The *-homomorphism condition M J M^* = J gives a right inverse, and diag(A, B^*) doubles any one-sided inverse
target: clifford-quantum-surjunctivity-iff-stable-finiteness
requires: []
artifacts:
  - experiments/quantum-surjunctivity-2026-09-17/clifford_star_f2.py
  - experiments/quantum-surjunctivity-2026-09-17/clifford_star_f2-output.txt
---

This is a self-contained proof. Write `S = F_p[G]`, `omega = exp(2 pi i / p)`, and `eps(x)` for the coefficient of
`e` in `x` in `S`.

**Weyl calculus.**
- `W(u) W(v) = omega^(beta(u,v)) W(v) W(u)`, where `beta(u, v) = eps(u J v^*)` is the standard symplectic form
  summed over sites.
- `W(u)^* = (phase) W(-u)` and `W(u+v) = (phase) W(u) W(v)`.
- The `W(u)` are unitaries, span a dense *-subalgebra of `A`, and are trace-orthonormal:
  `tau(W(u)^* W(v)) = delta_(u,v)`.
- The shift acts by `alpha_h W(u) = W(hu)`.

**Step 1 (Clifford automaton gives M).** Let `Phi(W(e_k)) = c_k W(m_k)` for the `2n` basis vectors `e_k` at `e`,
and let `M` be the matrix with rows `m_k`.
- By equivariance `Phi(W(g e_k)) = c_k W(g m_k)`.
- `W(u)` is, up to phase, a product of the `W(g e_k)^(u_k(g))`, so `Phi(W(u)) = (phase) W(uM)`.
- `Phi` preserves commutation phases, so `eps(u (M J M^* - J) v^*) = 0` for all `u, v`.
- Taking `u = g e_k` and `v = e_l` shows that every coefficient of `M J M^* - J` vanishes.

**Step 2 (M gives a Clifford automaton).** Given `M J M^* = J`, set `T(g, k) = W(g e_k M)`.
- Each `T(g, k)` is unitary with `T^p = 1`, by the choice of `lambda`.
- The pairwise commutation phases of the `T` are those of the `W(g e_k)`, because `beta(uM, vM) = beta(u, v)`.
- `M_p` is the universal C*-algebra of `x, z` with `x^p = z^p = 1` and `z x = omega x z`. So for finite `F`, the
  assignment `X_(g,i) -> T(g, i)`, `Z_(g,i) -> T(g, n + i)` extends to a unital *-homomorphism `A_F -> A`. A copy of
  `M_p` sits at each site, and copies at different sites commute; the phase `omega` within a site is checked
  above.
- These homomorphisms are compatible and isometric, since `A_F` is simple. They extend to `Phi` on `A`, which is
  equivariant and has finite propagation because `M` has finite support.

**Step 3 (right inverse).** `M (J M^* J^-1) = I` follows from `M J M^* = J`. So `R = J M^* J^-1` is a right
inverse, and `u -> uM` is injective on `S^(2n)`.

**Step 4 (onto iff left invertible).**
- If `L M = I`, then `L = L M R = R`. Every `v` equals `(vR) M`, so every `W(v)` lies in `Phi(A)`. The `W(v)` span a
  dense subspace and `Phi(A)` is closed, so `Phi` is onto.
- If `M` has no left inverse, then some `e_k` is not of the form `lM`, so `v = e_k` is not in `S^(2n) M`.
- `Phi(A)` is the closure of the span of the `W(uM)`, and each of these is trace-orthogonal to `W(v)`. So
  `tau(W(v)^* y) = 0` for all `y` in `Phi(A)`. But `tau(W(v)^* W(v)) = 1`, so `W(v)` is not in `Phi(A)`.

**Step 5 (equivalence).**
- **If `S` is stably finite.** For every Clifford automaton, `M R = I` gives `R M = I`, so `Phi` is onto by Step 4.
- **If `S` is not stably finite.** There are `k` and `A, B` in `M_k(S)` with `AB = I` and `BA != I`. Take `n = k`
  and `M = diag(A, B^*)`. Then

      M J M^* = [[0, -A B], [B^* A^*, 0]] = [[0, -I], [(AB)^*, 0]] = J,

  so Step 2 gives a Clifford automaton.
- If `L M = I` with `L = [[L_11, L_12], [L_21, L_22]]`, the top-left block reads `L_11 A = I`. Then
  `L_11 = L_11 A B = B`, so `BA = I`, which is a contradiction. By Step 4 this automaton is not onto.

**Remark (F_2 star computation).** `clifford_star_f2.py` enumerates the Weyl pairs `(Phi(X), Phi(Z))` on `{1, a, b}`
that satisfy Step 1's conditions over `F_2 = <a, b>`, for `n = 1` and `p = 2, 3, 5`.
- Each translate `hN` with `h != e` meets `N` in a single site, so the conditions are one-site symplectic products.
- The solutions number `3 |Sp_2(F_p)|`, and all are single-slot. The corresponding `M` is `s` times a unit of
  `M_2(F_p)` with `s` in `{1, a, b}`.
- This agrees with Step 5, since `F_p[F_2]` is stably finite (`F_2` is sofic).
