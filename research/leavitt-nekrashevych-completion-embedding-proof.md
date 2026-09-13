---
rg: 2
id: leavitt-nekrashevych-completion-embedding-proof
kind: route
title: Represent O_psi on a countable direct sum of copies of its core by an Eilenberg swindle
requires: []
target: leavitt-nekrashevych-completion-embeds-and-is-fp
---

Notation as in the claim.

## 1. Finite presentation

Let `O'` be the algebra given by the finite presentation in part 1. It maps onto
`O_psi`. Conversely, in `O'` let `B_0` be the set of `b in B` (images of elements
of the free algebra on the `g_k` modulo `R`) satisfying
`b = sum_{ij} s_i psi(b)_{ij} t_j`. Then:

- `1 in B_0`, since `psi(1) = I_d` and `sum_i s_i t_i = 1`;
- `B_0` is closed under linear combinations;
- `B_0` is closed under products: for `a, b in B_0`,
  `a b = sum_{i,j,k,l} s_i psi(a)_{ij} t_j s_k psi(b)_{kl} t_l
       = sum_{i,j,l} s_i psi(a)_{ij} psi(b)_{jl} t_l
       = sum_{i,l} s_i psi(ab)_{il} t_l`,
  using `t_j s_k = delta_{jk}` and that `psi` is a homomorphism.

So `B_0` is a unital subalgebra containing every `g_k`, hence `B_0 = B`. Every
defining relator of `O_psi` holds in `O'`, so `O' = O_psi`.

## 2. If psi is not injective, B -> O_psi is not injective

If `psi(b) = 0` then `b = sum s_i psi(b)_{ij} t_j = 0` in `O_psi`.

## 3. The core C and the split isomorphism Phi

Assume `psi` is injective. Index `M_{d^n}(B)` by pairs of words of length `n` in
`{1..d}`. Define `Psi_n : M_{d^n}(B) -> M_{d^{n+1}}(B)` by

```text
Psi_n(X)_{(alpha i),(beta j)} = psi(X_{alpha beta})_{ij},
```

that is, `psi` applied entrywise with the new letter appended at the end. Each
`Psi_n` is an injective unital algebra homomorphism, with `Psi_0 = psi`. Let

```text
C = lim_n ( M_{d^n}(B), Psi_n ),
```

a unital algebra into which `B = M_{d^0}(B)` embeds, because all connecting maps
are injective.

Regroup indices by the *first* letter: `M_{d^{n+1}}(B) = M_d(M_{d^n}(B))`, with block
`(i,j)` indexed by `(i alpha', j beta')`. Call this algebra isomorphism `Phi_{n+1}`.
Appending letters at the end commutes with grouping by the first letter:
block `(i,j)` of `Psi_{n+1}(X)` equals `Psi_n` of block `(i,j)` of `X`. So the
`Phi_{n+1}` induce an algebra isomorphism

```text
Phi : C -> M_d(C),     with   Phi(b) = psi(b)  for b in B,
```

because `b` at level 0 equals `psi(b)` at level 1, and `Phi_1(psi(b)) = psi(b)` in
`M_d(M_{d^0}(B)) = M_d(B)`.

## 4. A C-module V with V isomorphic to its twisted d-th power

For a left `C`-module `W`, write `W^(d)_Phi` for `W^d` (columns) with `x in C`
acting by the matrix `Phi(x)`, whose entries act on `W`.

- `Phi` is an isomorphism from the regular left module `C` to `M_d(C)` with `x`
  acting by left multiplication by `Phi(x)`, since `Phi(xv) = Phi(x) Phi(v)`.
- `M_d(C)` is the direct sum of its `d` columns, and each column is `C^(d)_Phi`.
  So `C ≅ (C^(d)_Phi)^{⊕ d}` as left `C`-modules.
- Let `V = ⊕_{m in N} C`. Then `V ≅ ⊕_{N × {1..d}} C^(d)_Phi ≅ ⊕_{N} C^(d)_Phi`,
  choosing a bijection `N × {1..d} -> N`.
- Also `V^(d)_Phi = ⊕_N C^(d)_Phi`, since `Phi(x)` acts coordinatewise in `m`.

So there is a `C`-linear isomorphism `theta : V -> V^(d)_Phi`, meaning
`theta(x v) = Phi(x) theta(v)`.

## 5. The representation

Let `iota_j : V -> V^d` be the `j`-th coordinate inclusion and `pi_i : V^d -> V`
the `i`-th projection. In `End_K(V)` put

```text
s_j = theta^{-1} ∘ iota_j,     t_i = pi_i ∘ theta,     b = left multiplication L_b.
```

- `t_i s_j = pi_i iota_j = delta_{ij} id`.
- `sum_i s_i t_i = theta^{-1} ( sum_i iota_i pi_i ) theta = id`.
- For `b in B`: `sum_{ij} s_i L_{psi(b)_{ij}} t_j = theta^{-1} (Phi(b) ·) theta = L_b`,
  by `C`-linearity of `theta` and `Phi(b) = psi(b)`.
- `B` acts through the algebra homomorphism `B -> C -> End_K(V)`.

So these operators define a homomorphism `O_psi -> End_K(V)` extending
`b |-> L_b`. For `b ≠ 0` in `B`, `b ≠ 0` in `C` (section 3), and
`L_b(1,0,0,...) = (b,0,0,...) ≠ 0`. Hence `B -> O_psi` is injective. This proves
part 2.
