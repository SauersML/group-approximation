---
rg: 2
id: positive-char-polynomial-affine-groups-are-self-similar-proof
kind: route
title: Send s_1 to the uniformizer, evaluate the other variables at a parameter, and substitute s_i -> a_i + s_1 s_i in the states
target: positive-char-polynomial-affine-groups-are-self-similar
requires: []
---

Direct proof (2026-09-13, lane `bh-metabelian`). Write `G = R^n x| Γ`,
`O = F_p[[u]]` and `X = O^n x O^(k-1)`.

**1. Action.** `P -> P<a>` is a unital ring homomorphism `R -> O`. So

```text
(g,b)·((g',b')·(v,a)) = (g<a>g'<a>v + g<a>b'<a> + b<a>, a) = (gg', gb'+b)·(v,a).
```

**2. Tree.**
- Every `x in O` has a unique expansion `x = x_0 + u x'` with `x_0 in F_p`.
  Iterating identifies `X` with the boundary of the rooted tree whose level `j` is
  `X / u^j X`. Each vertex has `p^(n+k-1)` children.
- `P<a> mod u^j` depends only on `a mod u^j`, because `P` has coefficients in
  `F_p` and `u^j O` is an ideal. So every element of `G`, and its inverse, permutes
  each level compatibly with the projections. So `G` acts by tree automorphisms.

**3. Faithful.** Suppose `(g,b)` acts trivially.
- **The translation.** At `v = 0`, each coordinate `b_i` has `b_i<a> = 0` for
  every `a in O^(k-1)`.
  - Write `b_i = Σ_μ c_μ(s_1) s_2^(μ_2) ... s_k^(μ_k)` with `c_μ in F_p[s_1]`.
  - The map `F_p[s_1] -> O`, `s_1 -> u`, is injective. So `b_i` gives the
    polynomial `Σ_μ c_μ(u) y^μ in O[y_2, ..., y_k]`, which vanishes at every point
    of `O^(k-1)`.
  - `O` is an infinite integral domain. By induction on the number of variables, a
    polynomial over an infinite domain that vanishes everywhere is zero: a nonzero
    polynomial in one variable has finitely many roots.
  - So every `c_μ(u) = 0`, hence every `c_μ = 0`, and `b = 0`.
- **The linear part.** Then `g<a> v = v` for all `v` and `a`. So every entry of
  `g - I` vanishes at every `a`, and `g = I` by the same argument.

**4. States.**
- **Substitution.** For `P in R`,
  `σ_α(P) = P(s_1, α_2 + s_1 s_2, ..., α_k + s_1 s_k)`. So for `a' in O^(k-1)`

  ```text
  σ_α(P)<a'> = P(u, α + u a') = P<α + u a'>.
  ```

- **Divisibility.** Setting `s_1 = 0` in `σ_α(P)` gives the constant `P(0,α)`. A
  polynomial in `F_p[s_1, ..., s_k]` that vanishes at `s_1 = 0` is divisible by
  `s_1`. So `σ_α(P) - P(0,α) in s_1 R`.
  - With `c = g(0,α)e + b(0,α)`, this gives `σ_α(g)e + σ_α(b) = c + s_1 w` for a
    unique `w in R^n`.
- **The computation.** For `x = (e + u v', α + u a')`,

  ```text
  g<α+ua'>(e + u v') + b<α+ua'>
     = σ_α(g)<a'> e + σ_α(b)<a'> + u σ_α(g)<a'> v'
     = c + u ( σ_α(g)<a'> v' + w<a'> ),
  ```

  using `s_1<a'> = u`.
- **Reading off.** So `(g,b)` sends the first-level vertex `(e,α)` to `(c,α)`.
  Under the identification `(e + u v', α + u a') <-> (v', a')` of the subtree with
  the whole tree, it acts as `(σ_α(g), w)`.
- **The state lies in `G`.** `σ_α` is a unital ring endomorphism of `R`. So it sends
  each elementary matrix `e_ij(r)` to `e_ij(σ_α(r))`, hence `σ_α(E_n(R)) ⊆ E_n(R)`,
  and `det σ_α(g) = σ_α(det g) = 1` when `g in SL_n(R)`. And `w in R^n`.

**5. Conclusion.** `G <= Aut(T_d)` with `d = p^(n+k-1)`, and every level-1 state of
every element lies in `G`. This is Zaremsky's definition, read from the extracted
text of arXiv:2405.09722 on MSI
(`/scratch.global/sauer354/bh-reviewer/2405.09722.txt`, l.109--110):
"Definition 2.1 (Self-similar). A subgroup G ≤ Aut(T_d) is self-similar if its
image in S_d ≀_d Aut(T_d) under the above isomorphism is contained in S_d ≀_d G." ∎
