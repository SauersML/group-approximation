---
rg: 2
id: triangle-edge-matching-one-edge-holonomy-proof
kind: route
title: Equalize edge eigenvalue counts with linear characters, align two edges by near-identity intertwiners, and feed the third edge to (HA)
target: triangle-edge-matching-reduces-to-one-edge-holonomy
requires:
  - triangle-of-finite-groups-hs-stability-is-edge-matching
---

Norms `||·||_{2,k}` on `M_k` are normalized by `k`; `||·||_op` is the operator norm. `ζ = e^(2πi/p)`.

## (EM) ⇒ (HA)

(HA) data satisfy the hypotheses of (EM), with the `b` and `a` mismatches equal to `0`.

## (HA) ⇒ (EM)

Let `ρ_i = ρ_{i,n}` on `C^d`, `d = d_n`, with all three edge mismatches at most `ε = ε_n → 0`.

**Spectral projections.** For a representation `U` of `Z/p` (a unitary with `U^p = I`), put
`P_k(U) = (1/p) Σ_{j=0}^{p−1} ζ^(−kj) U^j`, the spectral projection for `ζ^k`. For two such unitaries,
`||U^j − V^j||_2 ≤ j ||U − V||_2` by telescoping, so

```text
||P_k(U) − P_k(V)||_2 ≤ (1/p) Σ_j j ||U − V||_2 = ((p−1)/2) ||U − V||_2.
```

The normalized trace norm is at most the normalized HS norm, so the eigenvalue multiplicities
`μ_k(U) = tr P_k(U)` satisfy `|μ_k(U) − μ_k(V)| ≤ d (p−1) ||U − V||_2 / 2`.

**(L1) Padding by linear characters.**
1. Put `δ_b = μ(ρ_0(b)) − μ(ρ_1(b))`, `δ_a = μ(ρ_0(a)) − μ(ρ_2(a))`, `δ_c = μ(ρ_1(c)) − μ(ρ_2(c))`,
   vectors in `Z^p` with coordinate sum `0` (equal dimensions). Let `M = max_e ||δ_e||_∞`, so
   `M ≤ d(p−1)ε/2`.
2. If `M = 0`, set `m = 0`. Otherwise let `t = p⌈M/p⌉ ≤ M + p ≤ (p+1)M`, `u = t·(1,…,1) ∈ Z^p`,
   and `m = pt`. Then `m ≤ p(p+1)M ≤ p(p^2−1) ε d / 2`.
3. Prescribe marginals:
   - `S_0` on `X_0`: `a`-counts `u`, `b`-counts `u`;
   - `S_1` on `X_1`: `c`-counts `u`, `b`-counts `u + δ_b`;
   - `S_2` on `X_2`: `c`-counts `u + δ_c`, `a`-counts `u + δ_a`.

   All entries are nonnegative since `t ≥ M`, and each pair of marginals has total `m`.
4. **Realization.** For each vertex, a `p × p` nonnegative integer matrix with the two prescribed
   marginals exists (the transportation polytope with equal totals has integer points, e.g. by the
   northwest-corner rule; for `S_0` take the constant matrix `t/p`). By (SPLIT), each entry
   `(j,k)` of that matrix is realized by that many copies of the linear character with eigenvalues
   `(ζ^j, ζ^k)` on the two edge generators. So `S_i` is a genuine representation of `X_i` on `C^m`.
5. **Counts now agree.** On `b`: `μ(ρ_0(b)) + u = μ(ρ_1(b)) + u + δ_b`. On `a` and `c` likewise.
   So `ρ'_i = ρ_i ⊕ S_i` on `C^(d+m)` have equal multiplicity vectors on every edge.
6. **Mismatch after padding.** The padded blocks differ by at most `2` in operator norm on `m`
   coordinates, so every edge mismatch of the `ρ'_i` is at most
   `η = ε + 2 (m/(d+m))^(1/2) → 0`.

**(L2) Alignment.** Let `U, V` be representations of `Z/p` on `C^D` with equal multiplicities and
`||U − V||_2 ≤ η`.
1. Put `T = (1/p) Σ_{j=0}^{p−1} U^j V^(−j)`. Then `UT = TV`, `||T||_op ≤ 1`, and
   `||T − I||_2 ≤ (1/p) Σ_j j η = τ := (p−1)η/2`.
2. `K = ker T` is `V`-invariant and `R = ran T` is `U`-invariant. `T*T` commutes with `V`
   (from `TV* = U*T`). In the polar decomposition `T = W|T|`, `W : K^⊥ → R` is a unitary
   intertwiner from `V|_(K^⊥)` to `U|_R`. So these have equal multiplicities, hence so do `V|_K`
   and `U|_(R^⊥)`. Choose a unitary intertwiner `W' : K → R^⊥` and set `w = W ⊕ W'`, so
   `wVw* = U`.
3. **Estimates.**
   - Each unit vector `k ∈ K` has `||(T−I)k|| = 1`, so `dim K / D ≤ ||T − I||_2^2 = τ^2`.
   - `||(I − |T|)|_(K^⊥)||_2 ≤ ||I − T*T||_2 ≤ ||T*||_op ||I − T||_2 + ||I − T*||_2 ≤ 2τ`, using
     `|1 − s| ≤ |1 − s^2|` for `s ≥ 0`.
   - `||w − T||_2^2 = ||W(I − |T|)|_(K^⊥)||_2^2 + dim K/D ≤ 5τ^2`.
   - So `||w − I||_2 ≤ (√5 + 1) τ ≤ 3.24 (p−1) η / 2`.

**Aligning two edges.**
1. Apply (L2) to `U = ρ'_0(b)`, `V = ρ'_1(b)`. This gives `w_1` with `||w_1 − I||_2 ≤ C_p η`; put
   `ρ''_1 = w_1 ρ'_1 w_1*`, a genuine representation of `X_1` with `ρ''_1(b) = ρ'_0(b)`.
2. Apply (L2) to `ρ'_0(a)` and `ρ'_2(a)`, giving `w_2`; put `ρ''_2 = w_2 ρ'_2 w_2*`, so
   `ρ''_2(a) = ρ'_0(a)`. Put `ρ''_0 = ρ'_0`.
3. Conjugation moves every matrix of norm `≤ 1` by at most `2||w − I||_2`. So
   `||ρ''_1(c) − ρ''_2(c)||_2 ≤ η + 4 C_p η → 0`, and `||ρ''_i(x) − ρ'_i(x)||_2 ≤ 2 C_p η → 0`.

**Applying (HA).** The `ρ''_i` are (HA) data on `C^(d+m)`. (HA) gives genuine `π : G → U(D)`,
`D/(d+m) → 1`, with `||ρ''_i(x) − P' π(x) P'*||_{2,d+m} → 0`, where `P'` compresses to `C^(d+m)`.

**Back to `C^d`.**
1. `||ρ'_i(x) − P' π(x) P'*||_{2,d+m} ≤ ||ρ'_i(x) − ρ''_i(x)||_2 + ||ρ''_i(x) − P'π(x)P'*||_2 → 0`.
2. `ρ'_i = ρ_i ⊕ S_i` is block diagonal, so compressing to `C^d` returns `ρ_i(x)` exactly. With `P`
   compressing `C^D` to `C^d`,
   `||ρ_i(x) − Pπ(x)P*||_{2,d} ≤ ((d+m)/d)^(1/2) ||ρ'_i(x) − P'π(x)P'*||_{2,d+m} → 0`.
3. `D/d = (D/(d+m))(1 + m/d) → 1`, since `m/d ≤ p(p^2−1)ε/2 → 0`.

This is (EM). The final sentence of the claim is
`triangle-of-finite-groups-hs-stability-is-edge-matching`. ∎
