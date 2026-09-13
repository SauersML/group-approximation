---
rg: 2
id: subshift-el-group-centre-detects-rational-eigenvalues-proof
kind: route
title: Scalars in rational spectrum are unit commutators, and periodic finite models force the rest to have determinant one
target: subshift-el-group-centre-detects-rational-eigenvalues
requires: [minimal-subshift-algebra-is-simple-lef-ring]
artifacts:
  - research/artifacts/sk-coefficients-proposal-2026-09-13.md
---

Notation: `R = LC(X,F_q) ⋊_T Z`, with `u f u^{-1} = f∘T^{-1}`, and `G = EL_n(R)`, `n ≥ 3`. Input from `minimal-subshift-algebra-is-simple-lef-ring`: `Z(R) = F_q`.

**(a) `Z(G) ⊆ F_q^× I_n`.** A central g commutes with every `e_ij(1)`, so `g = cI_n` with `c ∈ R`. It commutes with every `e_ij(r)`, so `c ∈ Z(R) = F_q`, and c is a unit.

**(b) `E_X(q) = μ_e`.**
- Let `φ: X → Z/d` be a factor map, `d | q−1`, and `ζ ∈ F_q^×` of order d. Then `f = ζ^φ` is continuous with `f∘T = ζ f`.
- Conversely, suppose `f∘T = λ f` with `ord(λ) = d`. Then `x ↦ f(x)μ_d` is T-invariant and locally constant, hence constant by minimality. So `f = aψ` with `ψ: X → μ_d` and `ψ∘T = λψ`. ψ is onto by minimality, and so it is a factor map onto `Z/d`.
- If `X → Z/d_1` and `X → Z/d_2` are factors, the image of `X → Z/d_1 × Z/d_2` is the orbit of one point, which has size `lcm(d_1,d_2)`. So the divisors d of `q−1` with a factor `X → Z/d` are closed under lcm and have a largest element e.
- `E_X(q)` is a subgroup of the cyclic group `F_q^×` (multiply eigenfunctions). It contains exactly the elements of order dividing e, so `E_X(q) = μ_e`.

**(c) Whitehead reductions.**
- For a unit v, `diag(v, v^{-1}) = e_12(v) e_21(−v^{-1}) e_12(v) · e_12(−1) e_21(1) e_12(−1) ∈ E_2(R)`.
- For units a, b: `diag(aba^{-1}b^{-1}, 1) = diag(a,a^{-1}) diag(b,b^{-1}) diag((ba)^{-1}, ba) ∈ E_2(R)`.
- For `c ∈ F_q^×`, `cI_n = diag(c^n, 1, …, 1) · Π_{i=2}^n D_i`, where `D_i` is `diag(c^{-1}, c)` in positions `(1,i)` and lies in `E_n(R)`. So `cI_n ∈ G ⟺ diag(c^n,1,…,1) ∈ G`.

**(d) `c^n ∈ E_X(q) ⇒ cI_n ∈ G`.**
- Let `λ = c^n` with `f∘T = λ f`, so `f(x) = λ f(T^{-1}x)`.
- `u f^{-1} u^{-1} = f^{-1}∘T^{-1}`, so `f u f^{-1} u^{-1} = f/(f∘T^{-1}) = λ`.
- By (c), `diag(λ,1,…,1) ∈ E_2(R) ⊆ G`, and then `cI_n ∈ G`.

**(e) `cI_n ∈ G ⇒ c^n ∈ E_X(q)`.**
- Fix a product of elementary matrices equal to `cI_n`. Let `k_0` exceed the radii of all local functions occurring in the ring computation of that product, shifts included.
- Let v be a word of X of length `2k ≥ 2k_0` occurring at positions `i < i+N` of some `x ∈ X`, and put `w = x_{[i, i+N)}`, `y = w^∞`.
  - Every window of length 2k+1 of y lies in some `x_{[i+p, i+p+2k+1)}`: the positions past the end of w repeat the prefix v of w, by induction on the number of seams.
  - So every such window is a word of X.
- Let `D_y(f)` be the diagonal matrix on `F_q^{Z/N}` with entries `f` evaluated along y (well defined for radius ≤ k, since the windows are words of X). Let `Pδ_t = δ_{t+1}`.
  - `ψ_y(Σ f_j u^j) = Σ D_y(f_j) P^j` satisfies `P^i D_y(f) P^{-i} = D_y(f∘T^{-i})`.
  - So it preserves every sum and product in the fixed computation; exponents add modulo N consistently.
- Entrywise, `ψ_y(cI_n) = cI_{nN}` equals a product of matrices `I + ψ_y(r)E_ij` (`i ≠ j`), each of determinant 1. So `c^{nN} = 1`.
- Let `d = ord(c^n)`. `ord(c) | nN` is equivalent to `d | N`. So d divides every difference of two occurrences of v in a point of X.
- `φ(x) = −i mod d`, for any occurrence i of v in x, is therefore well defined.
  - It is continuous, because v occurs within a bounded distance of 0 by uniform recurrence.
  - It satisfies `φ(Tx) = φ(x)+1`.
- So `(X,T)` factors onto `Z/d`. `d | q−1` because `c^n ∈ F_q^×`, so `c^n ∈ μ_d ⊆ E_X(q)` by (b).

**(f)** By (a), (c), (d) and (e), `Z(G) = {cI_n : c^n ∈ μ_e}`. In the cyclic group `F_q^×`, `c^n ∈ μ_e ⟺ c^{ne} = 1 ⟺ c ∈ μ_{gcd(ne, q−1)}`. ∎
