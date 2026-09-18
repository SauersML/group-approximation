---
rg: 2
id: free-generalized-wreath-over-residually-finite-group-is-mf-proof
kind: route
title: Slow unitary bumps along Schreier graphs of finite quotients represent the free lamps covariantly, one block per word
target: free-generalized-wreath-over-residually-finite-group-is-mf
requires:
  - free-kernel-tree-actions-embed-in-free-generalized-wreath
---

The theorem uses no graph input. The requirement is used only for the corollary. Classical inputs:
- free groups are residually finite;
- a unitary `u` is `exp(A)` with `A` skew-Hermitian and `||A|| <= π`;
- `||exp(sA) - exp(s'A)|| <= |s-s'| ||A||`.

## 0. Notation

- *Orbits.* Write `X = ⊔_(o ∈ O) Q x_o` with `O` countable. Put `H_o = Stab_Q(x_o)`, and for every
  `x ∈ X` fix a representative `r_x ∈ Q` with `x = r_x x_o`, `o = o(x)`.
- *Generating sets.* For each `o`, fix finite symmetric sets `1 ∈ T_(o,1) ⊆ T_(o,2) ⊆ ...` with union
  `H_o`. If `H_o` is finite, eventually take `T_(o,n) = H_o`.
- *The free lamp group.* `F = *_X Z` is the free group on the set `X`. Enumerate its nontrivial
  elements `f_1, f_2, ...` and the nontrivial elements `h_1, h_2, ...` of `Q`.
- *Representations of the words.* For each `k`, let `S_k ⊆ X` be the finite set of letters occurring
  in the reduced form of `f_k`. Since free groups are residually finite, choose a finite-dimensional
  unitary representation `π_k` of the free group `F(S_k)` on `C^(m_k)` with `π_k(f_k) != 1` (a
  permutation representation on a finite quotient). Write `π_k(z) = exp(A_(k,z))` with `A_(k,z)`
  skew-Hermitian and `||A_(k,z)|| <= π`, for `z ∈ S_k`.

## 1. Choice of finite quotients

Fix `n`. Let `B_(o,n)` be the finite set of elements of `H_o` that are products of at most `3n`
elements of `T_(o,n)`. Consider the finite set `P_n` of elements

```text
h_i                              (i <= n),
r_z^(-1) r_(z') w^(-1)           (k <= n; z != z' in S_k; o(z) = o(z') = o; w ∈ B_(o,n)).
```

Each is nontrivial. For the second kind, `r_z^(-1) r_(z') = w ∈ H_o` would give `z' = r_(z') x_o =
r_z w x_o = r_z x_o = z`. Residual finiteness gives a finite quotient `q_n : Q -> F_n` with
`q_n(p) != 1` for all `p ∈ P_n`.

On `F_n`, let `G_(o,n)` be the Schreier graph with edges `y ~ q_n(t) y` for `t ∈ T_(o,n)`, and
`dist_(o,n)` its path metric (value `∞` between components).

**Separation.** For `k <= n` and distinct `z, z' ∈ S_k` in one orbit `o`, put
`p_z = q_n(r_z)^(-1)`. Then `dist_(o,n)(p_z, p_(z')) > 3n`.

Proof: a path of length `<= 3n` gives `w ∈ B_(o,n)` with `q_n(w) p_(z') = p_z`, i.e.
`q_n(r_z^(-1) r_(z') w^(-1)) = 1`, contrary to the choice of `q_n`.

## 2. The stage-n operators

Put `φ_n(s) = max(1 - s/n, 0)`, which is `1/n`-Lipschitz, and let `λ_n` be the left regular
representation of `F_n`.

*The block for one word.* For `k <= n` and each orbit `o`, define `B^(k)_(o,n) : F_n -> U(m_k)` by:
- `B^(k)_(o,n)(y) = exp( φ_n(dist_(o,n)(y, p_z)) A_(k,z) )` if `dist_(o,n)(y, p_z) < n` for some
  `z ∈ S_k` with `o(z) = o`;
- `B^(k)_(o,n)(y) = 1` otherwise.

By Separation the `n`-balls around the points `p_z` (`z ∈ S_k`, same orbit) are pairwise at
distance `> n`, so at most one `z` applies and `B` is well defined. Along an edge `y ~ y'` of
`G_(o,n)`:

```text
|| B^(k)_(o,n)(y) - B^(k)_(o,n)(y') ||  <=  π/n.                      (Lip)
```

Proof of (Lip):
- If both points lie in the open `n`-ball of one `p_z`, this is the Lipschitz bound for `φ_n`
  together with `||A|| <= π`.
- If exactly one lies in a ball, the other is at distance exactly `n`, where `φ_n = 0`. So the
  formula for that `z` also gives the value `1` there, and the same bound applies.
- The two points cannot lie in balls of different `z`, since the balls are at distance `> n >= 1`.
- If neither lies in a ball, both values are `1`.

*The stage-n operators.* The Hilbert space is
`\mathcal H_n = (+)_(k <= n) l^2(F_n) (x) C^(m_k)`, of finite dimension `d_n`. Define

```text
Λ_n(q)   = (+)_k  λ_n(q_n(q)) (x) 1,
V_(o,n)  = (+)_k  sum_(y ∈ F_n) e_yy (x) B^(k)_(o,n)(y),
U_(x,n)  = Λ_n(r_x) V_(o(x),n) Λ_n(r_x)^*  =  (+)_k  sum_(ω ∈ F_n) e_ωω (x) B^(k)_(o,n)(q_n(r_x)^(-1) ω).
```

All `V_(o,n)` and `U_(x,n)` are block diagonal over the points `ω ∈ F_n`.

## 3. The corona homomorphism

Let `\mathcal A = prod_n M_(d_n) / (+)_n M_(d_n)`, with `Λ(q) = [Λ_n(q)]`, `V_o = [V_(o,n)]` and
`U_x = [U_(x,n)]`.

- *`Λ` is a homomorphism.* Each `q_n` and `λ_n` is one, so `Λ : Q -> U(\mathcal A)` is a
  homomorphism.
- *`V_o` commutes with `Λ(H_o)`.* Fix `h ∈ H_o`. Then `h ∈ T_(o,n)` for all large `n`, and
  `Λ_n(h) V_(o,n) Λ_n(h)^* = (+)_k sum_y e_(hy,hy) (x) B^(k)_(o,n)(y)`. By (Lip) along the edges
  `y ~ q_n(h)y`, it differs from `V_(o,n)` by at most `π/n` in norm. So `[Λ(h), V_o] = 0`.
- *Covariance.* For `q ∈ Q` and `x ∈ X` with `o = o(x)`, put `h = r_(qx)^(-1) q r_x ∈ H_o`. Then

  ```text
  Λ(q) U_x Λ(q)^* = Λ(r_(qx)) Λ(h) V_o Λ(h)^* Λ(r_(qx))^* = U_(qx).
  ```

By the universal property of the free group `F` on `X`, `x ↦ U_x` defines a homomorphism
`U : F -> U(\mathcal A)`. Covariance says `Λ(q) U(f) Λ(q)^* = U(q·f)`. So

```text
Φ(f, q) = U(f) Λ(q)
```

is a homomorphism `W -> U(\mathcal A)`. At stage `n`, a representative of `Φ(f,q)` is the product
`\tilde U_n(f) Λ_n(q)` of the stage operators of the letters of `f`. Here `\tilde U_n(f)` is block
diagonal over `F_n`, and its fibre at `(k, ω)` is the corresponding word in the fibre values.

## 4. Injectivity

- **Case `q != 1`.** For large `n`, `q_n(q) != 1`. The operator `\tilde U_n(f) Λ_n(q)` maps the
  fibre over `ω` into the fibre over `q_n(q) ω != ω`, which is orthogonal to it. Hence
  `||(Φ_n(f,q) - 1) ξ|| = sqrt(2) ||ξ||` for every `ξ`. So the corona norm of `Φ(f,q) - 1` is at
  least `sqrt(2)`.
- **Case `q = 1`, `f = f_k != 1`.** Take `n >= k` and look at the fibre over `(k, ω = 1)`. For
  `z ∈ S_k`, the fibre value of `U_(z,n)` is `B^(k)_(o(z),n)(q_n(r_z)^(-1)) = B^(k)_(o(z),n)(p_z)`.
  Since `dist(p_z, p_z) = 0` and `φ_n(0) = 1`, this equals `exp(A_(k,z)) = π_k(z)`. So the fibre of
  `\tilde U_n(f_k)` is `π_k(f_k) != 1`, and
  `||Φ_n(f_k) - 1|| >= ||π_k(f_k) - 1|| > 0` for all `n >= k`. The lower bound is independent of
  `n`, so `Φ(f_k) != 1`.

So `Φ` is injective and `W` is MF.

## 5. Corollary

Item 1 of `free-kernel-tree-actions-embed-in-free-generalized-wreath` embeds `Γ` in
`Z ≀^*_(E^±(Y)) (Γ/Λ)`. Here `E^±(Y)` is countable because `Γ` is, and `Γ/Λ` is countable and
residually finite. Restrict `Φ`.

## Remarks

- *Where the construction lives.* The lamps are slow only along the Schreier graphs of the
  stabilizers. At a fixed point `ω` a lamp is a genuine, possibly large, unitary. This is why the
  defects are free-lamp commutators `[e_x, h]`, `h ∈ H_o`, and why the Kazhdan defect mechanism
  (`normal-kazhdan-defect-non-mf`) cannot act: no normal Kazhdan subgroup sits inside a free lamp
  group.
- *Why there is no trace statement.* The separating fibre is one point out of `|F_n|`. On
  expander Schreier graphs the bump must be nontrivial on a vanishing fraction of the points, so
  the models are useless in normalized Hilbert--Schmidt norm.
- *Why torsion lamps are different.* Finite-order lamps have finite spectrum and cannot be
  interpolated slowly (`commuting-lamp-quotient-not-mf`).

∎
