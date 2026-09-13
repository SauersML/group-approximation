---
rg: 2
id: subshift-el-group-centre-detects-rational-eigenvalues
kind: claim
title: The centre of EL_n(LC(X,F_q) ⋊ Z) is mu_gcd(ne, q−1), where e is the largest divisor of q−1 such that X factors onto Z/e
distinct_from:
  minimal-effective-steinberg-algebras-have-scalar-centre: that computes the centre of the ring; this determines exactly which scalar matrices lie in the elementary group over the subshift crossed product.
  subshift-elementary-group-is-simple-modulo-centre: that proves EL_3 over the subshift algebra is simple modulo its finite scalar centre without computing the centre; this computes the centre for every n ≥ 3 and every q.
artifacts:
  - research/artifacts/sk-coefficients-proposal-2026-09-13.md
---

**ESTABLISHED (unreviewed)** by `subshift-el-group-centre-detects-rational-eigenvalues-proof`.

**Statement.** Let X be an infinite minimal subshift, q a prime power, `n ≥ 3`, and
`G = EL_n(LC(X,F_q) ⋊_T Z)`. Put
`E_X(q) = {λ ∈ F_q^× : f∘T = λf for some continuous f: X → F_q^×}`. Then:
1. `E_X(q) = μ_e(F_q)`, where `e` is the largest divisor of `q − 1` such that `(X,T)` factors onto the rotation `(Z/e, +1)`;
2. `Z(G) = {cI_n : c ∈ F_q^×, c^n ∈ E_X(q)} = μ_{gcd(ne, q−1)}(F_q)·I_n`.

For every λ ∈ E_X(q) the scalar λ is a commutator of units: `λ = f u f^{-1} u^{-1}`.

**Examples.**
- q = 2: `Z(G) = 1`, as in the F_2 note.
- Sturmian X (e.g. Fibonacci): the continuous eigenvalues come from an irrational rotation and contain no nontrivial root of unity. So `e = 1` and `Z(G) = μ_{gcd(n,q−1)} I = Z(SL_n(F_q))`.
- Period-doubling subshift (0↦01, 1↦00), which factors onto every `Z/2^j`: `e = 2^{v_2(q−1)}`. For q = 3, n = 3, `Z(G) = {±I_3}`. So `−I_3 ∈ EL_3(LC(X,F_3) ⋊ Z)` although `det(−I_3) = −1` in F_3; for Sturmian X, `−I_3 ∉ G`.

So the order of the centre, `gcd(ne, q−1)`, is an isomorphism invariant of `EL_n(LC(X,F_q) ⋊ Z)` that depends on the rational spectrum of X.

**Novelty (bounded check).** The every-q manuscript (b965d63ba, `prop:center`) and write-up part 2 stop at `Z(G) = Λ I_3` with `Λ = {λ : λI_3 ∈ G}`. A grep of main for scalars in EL_n, coboundaries and rational eigenvalues in subshift contexts found no computation of Λ. No literature search was done.
