---
rg: 2
id: single-configuration-check-mark-group-is-lift-presented-proof
kind: route
title: Separator sections are powers of A, and inside a block only constant rays keep a word stable; there it is a word in two commuting elements
target: single-configuration-check-mark-group-is-lift-presented
requires: [lift-ideal-membership-is-decided-along-paths, rover-nekrashevych-fp-iff-finite-lift-presentation, lift-presented-automaton-groups-satisfy-boone-higman]
---

Notation of the claim. `F = F(A, A', Z, N)`, `N` the relator kernel, `M_0 = ⟨⟨[A',N],[Z,N]⟩⟩` and
`M = ⟨⟨[A',N],[Z,N]⟩⟩_lift`.

**Letter rules.** Each entry gives the output and the section on a received letter; missing entries
are "output = input".

```text
A    : 0 -> 1, Z      1 -> 0, A'     γ -> γ, 1
A'   : 0 -> 1, N      1 -> 0, A'     γ -> γ, 1
Z    : 0 -> 0, Z      1 -> 1, N      γ -> γ, 1
N    : 0 -> 0, N      1 -> 1, N      γ -> γ, A
A^-1 : 1 -> 0, Z^-1   0 -> 1, A'^-1  γ -> γ, 1
A'^-1: 1 -> 0, N^-1   0 -> 1, A'^-1  γ -> γ, 1
Z^-1 : 0 -> 0, Z^-1   1 -> 1, N^-1   γ -> γ, 1
N^-1 : 0 -> 0, N^-1   1 -> 1, N^-1   γ -> γ, A^-1
```

**0. Uniqueness and infinite orders.**
- *Uniqueness.* If `g = (g, a, b)` and `h = (h, a, b)`, then `g^{-1}h = (g^{-1}h, 1, 1)`, which fixes
  every word by induction on length. So `g = h`.
- *`A` has infinite order.* On `{0,1}^*`, `A` and `A'` act as the binary odometer `τ`, and `Z`, `N` act
  trivially.
- *`N` has infinite order.* `N^e|_γ = A^e`.

**1. The two relators.**
- *`[A', N]`.* Conjugation gives `A'NA'^{-1} = (A'NA'^{-1}, N, A)`:
  - at `0`, the sections are `A'|_1 · N|_1 · (A'|_1)^{-1}`;
  - at `1`, they are `A'|_0 · N|_0 · (A'|_0)^{-1} = N N N^{-1}`;
  - at `γ`, `1 · A · 1`.

  Since `N = (N, N, A)`, uniqueness gives `A'NA'^{-1} = N`.
- *`[Z, N]`.* `ZNZ^{-1} = (ZNZ^{-1}, N, A)`, so `ZNZ^{-1} = N` in the same way.

**2. Sections at γ.** Every state fixes `γ`, so every letter of `w` receives `γ`. Hence
`w|_γ = A^{e_N(w)}` as a word, where `e_N` is the exponent sum of `N`. If `w ∈ N`, then `w|_γ ∈ N` and
`A` has infinite order, so `e_N(w) = 0` and `w|_γ = 1` in `F`.

**3. Digit rays.** Let `w ∈ N`, `ξ ∈ {0,1}^ω`, and `w_n = w|_{ξ[0,n)}`, the letter sequences.

- *A decreasing count.* By the table, `A^{±}` goes to `Z^{±}` or `A'^{±}`; `A'^{±}` goes to `A'^{±}` or
  `N^{±}`; `Z^{±}` goes to `Z^{±}` or `N^{±}`; and `N^{±}` stays `N^{±}`. So the number `c(w_n)` of
  letters not of the form `N^{±}` never increases. There is `n_0 >= 1` with `c(w_n)` constant for
  `n >= n_0`. After the first step no `A^{±}` remains.
- *Stability.* For `n >= n_0` no letter changes type. The survival rules for the received digit are:
  - `A'` needs `1` and outputs `0`;
  - `A'^{-1}` needs `0` and outputs `1`;
  - `Z^{±}` needs `0` and outputs `0`;
  - `N^{±}` passes its input.

  So each letter maps to itself, and `w_n = w_{n_0} =: v`.
- *Case `c = 0`.* Then `v` is a word in `N^{±}`, equal in `F` to `N^e`, and a relator. So `e = 0` and
  `v = 1` in `F`.
- *Case `c > 0`.* The rightmost letter of `v` not of the form `N^{±}` receives `ξ_n` and keeps its
  type, so `ξ_n` is constant, `= ε`, for `n >= n_0`. The digit action of `v` is `τ^{e_{A'}(v)}`, so
  `e_{A'}(v) = 0`.
  - Read `v` from the right, starting with the received digit `r = ε`. When `r = 0` the allowed
    letters are `N^{±}`, `Z^{±}` and `A'^{-1}`, the last setting `r = 1`. When `r = 1` they are `N^{±}`
    and `A'`, the last setting `r = 0`.
  - **`ε = 0`.** With `e_{A'} = 0`, `v = U_k (A'N^{b_k}A'^{-1}) U_{k-1} ⋯ (A'N^{b_1}A'^{-1}) U_0` with
    `U_i ∈ F(Z,N)`. Modulo `⟨⟨[A',N]⟩⟩`, `v ≡ v' ∈ F(Z,N)`, and `v' ∈ N`.
    - The subgroup `⟨Z, N⟩`: a word `u(Z,N)` satisfies `u = (u(Z,N), u(N,N), u(1,A))`. So `u = 1`
      forces `e_N = 0` from the `γ`-coordinate and `e_Z + e_N = 0` from the `1`-coordinate.
    - Conversely, exponent sums zero put `u` in `[F(Z,N), F(Z,N)] = ⟨⟨[Z,N]⟩⟩`. So `v' ∈ M_0`, hence
      `v ∈ M_0`.
  - **`ε = 1`.** Balanced, `v = N^{b_k}(A'^{-1}U_kA')N^{b_{k-1}} ⋯ (A'^{-1}U_1A')N^{b_0}`, with
    `U_i ∈ F(Z,N)`. Modulo `⟨⟨[A',N]⟩⟩`, `v ≡ v'' ∈ F(Y, N)` with `Y = A'^{-1}ZA'`.
    - The recursion of `Y`: `Y` fixes `0` and `1`, with `Y|_0 = N`, `Y|_1 = Y`, `Y|_γ = 1`. So a
      word `u(Y,N)` has sections `u(N,N)`, `u(Y,N)`, `u(1,A)`, and `u = 1` forces
      `e_Y = e_N = 0`.
    - Hence `v'' ∈ ⟨⟨[Y,N]⟩⟩`. Also
      `[Y,N] = A'^{-1}[Z, A'NA'^{-1}]A' ≡ A'^{-1}[Z,N]A' (mod ⟨⟨[A',N]⟩⟩)`, which lies in `M_0`.
- *Conclusion.* Along every digit ray, `w_{n_0} ∈ M_0 ⊆ M`.

**4. Conclusion.** Let `w ∈ N` and `ξ ∈ {0,1,γ}^ω`.
- If `ξ` has its first `γ` at position `m`, then `w|_{ξ[0,m]}` is the `γ`-section of the relator
  `w|_{ξ[0,m)}`. By step 2 it equals `1` in `F`, so it lies in `M`.
- Otherwise step 3 applies.

By `lift-ideal-membership-is-decided-along-paths`, `w ∈ M`. So `N = M`, and the two relators lie in
`N` by step 1. Items 2 and 3 of the claim follow:
- *Theorem A* makes `V_3(C_2)` finitely presented.
- *Exponential activity* is the pair of loops of `N`.
- *Non-contraction* follows because `A^n|_{bγ} = A^n` whenever `b, …, b+n-1` avoid `0` and all ones.
- *The `Z ≀ Z` copy*: elements trivial on the first block act at each `bγ` by a power of `A`, so they
  form an abelian group. It is generated by the translates `A^j (Z^{-1}N) A^{-j}`, which are lamps at
  the points `j` of long blocks and are independent. `∎`
