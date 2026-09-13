---
rg: 2
id: polynomial-parameter-affine-groups-are-self-similar-proof
kind: route
title: Evaluate at a p-adic parameter and substitute t -> a + pt in the states
target: polynomial-parameter-affine-groups-are-self-similar
requires: []
artifacts:
  - research/artifacts/bh-sl3-zt-host-2026-09-12.md
---

Full details are in §1 of the artifact. Write `G = R^n x| Γ` and
`X = Z_p^n x Z_p^k`.

**1. Action.**
`(g,b)·((g',b')·(v,s)) = (g(s)g'(s)v + g(s)b'(s) + b(s), s) = (gg', gb'+b)·(v,s)`.

**2. Tree.** Writing `x = x_0 + p x'` with `x_0 in {0..p-1}^(n+k)` and iterating
identifies `X` with the boundary of the rooted `p^(n+k)`-regular tree. Level `j`
is `X / p^j X`. Polynomials with coefficients in `Z[1/m] ⊂ Z_p` preserve
congruence mod `p^j`. So each element and its inverse permute every level.

**3. Faithful.** Suppose `(g,b)` acts trivially.
- At `v = 0`, `b` vanishes on `Z_p^k`, so `b = 0`.
- Then `g(s) = I` for all `s`, so `g = I`.

**4. States.**
- `σ_a(f) - f(a) in pR` for every `f in R`, since `(a_j + p t_j)^c ≡ a_j^c mod pR`.
- Since `Z[1/m]/pZ[1/m] = F_p`, the vector `g(a)e + b(a)` has a digit
  `c in {0..p-1}^n`.
- Let `u = σ_a(g)e + σ_a(b)`. Then `u - c ≡ g(a)e + b(a) - c ≡ 0 mod pR`, so
  `w = (u - c)/p in R^n`.
- For `x = (e + pv', a + ps')`,

```text
g(a+ps')(e+pv') + b(a+ps') = c + p ( σ_a(g)(s') v' + w(s') ).
```

So the state at `(e,a)` is `(σ_a(g), w)`. It lies in `G`, since `σ_a` is a ring
map: `σ_a(E_n(R)) ⊆ E_n(R)` and `det σ_a(g) = σ_a(det g) = 1`.

**5. Conclusion.** `G <= Aut(T_(p^(n+k)))`, and its image lies in
`S_d ≀_d G` with `d = p^(n+k)`. This is Zaremsky's definition of a self-similar
group (arXiv:2405.09722v2, `def:ss`).
