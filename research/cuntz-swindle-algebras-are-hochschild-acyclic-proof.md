---
rg: 2
id: cuntz-swindle-algebras-are-hochschild-acyclic-proof
kind: route
title: The Cuntz pair turns the swindle into additivity of Hochschild homology, and an isometry of the relative commutant into the first range would make the swindle inner
target: cuntz-swindle-algebras-are-hochschild-acyclic
requires: []
---

Notation as in the target. Write `x^*` for the named partner of `x`; no involution on
`A` is assumed. `C_n(A) = A^(⊗(n+1))` with the Hochschild boundary `b`. The boundary uses
only products, so every multiplicative `k`-linear map `f : A -> A'` of unital algebras,
unital or not, gives a chain map `f^⊗` and a map `HH(f)`. The same holds for Connes'
cyclic complex, since `f^⊗` commutes with the cyclic operator.

**Imports (textbook, Loday, *Cyclic Homology*, 2nd ed., Sections 1.2 and 2.2; statement
checked, numbering not quoted).**
- (I1) *Morita invariance.* The generalized trace
  `Tr(m_0 ⊗ ... ⊗ m_n) = Σ (m_0)_(i_0 i_1) ⊗ (m_1)_(i_1 i_2) ⊗ ... ⊗ (m_n)_(i_n i_0)`
  is a chain map `C_*(M_r(A)) -> C_*(A)`, compatible with the cyclic operator. It
  satisfies `Tr ∘ ι_1^⊗ = id`, where `ι_1(a) = a E_11`, and `HH(ι_1)`, `HC(ι_1)` are
  isomorphisms. Hence `HH(Tr) = HH(ι_1)^(-1)`, and likewise for `HC`.
- (I2) *Inner invariance.* For a unit `u` of a unital algebra `B`, conjugation `Ad u`
  induces the identity on `HH_*(B)` and on `HC_*(B)`. In degree 0 the homotopy is
  `a_0 |-> a_0 u^(-1) ⊗ u`, with `b(a_0 u^(-1) ⊗ u) = a_0 − u a_0 u^(-1)`.

Everything below holds verbatim with `HC` in place of `HH`.

## Step 1. Conjugation by an isometry is the identity on HH

Let `s, s^* ∈ A` with `s^* s = 1`, and `ψ_s(a) = s a s^*` (multiplicative, not unital).
Put `f = 1 − s s^*`. Then `f^2 = f`, `f s = 0`, `s^* f = 0`. In `M_2(A)` let

```text
U = [ s   f  ]      U' = [ s^*  0 ]
    [ 0  s^* ]           [ f    s ]
```

Direct multiplication, using the three identities, gives `U U' = U' U = I_2`. And
`U ι_1(a) U' = [[s a s^*, 0], [0, 0]] = ι_1(ψ_s(a))`. So `ι_1 ∘ ψ_s = Ad U ∘ ι_1`, and by
(I2) `HH(ι_1) HH(ψ_s) = HH(ι_1)`. Since `HH(ι_1)` is an isomorphism (I1),
`HH(ψ_s) = id`.

## Step 2. The Cuntz pair identifies M_2(A) with A

Let `Φ : M_2(A) -> A`, `Φ(m) = Σ_(i,j) s_i m_ij s_j^*`. The relations `s_i^* s_j = δ_ij`
and `Σ s_i s_i^* = 1` make `Φ` a unital algebra isomorphism, with inverse
`a |-> (s_i^* a s_j)_(ij)`. Also `Φ ∘ ι_1 = ψ_(s_1)`. By Step 1,
`HH(Φ) HH(ι_1) = id`, so `HH(Φ) = HH(ι_1)^(-1) = HH(Tr)`.

## Step 3. Additivity

For unital endomorphisms `α, β` of `A`, let `Δ(a) = diag(α(a), β(a))`, a unital map
`A -> M_2(A)`. Then `α ⊞ β = Φ ∘ Δ`. On chains, `Tr(Δ(a_0) ⊗ ... ⊗ Δ(a_n))` keeps only the
index strings `i_0 = ... = i_n`, because every `Δ(a_j)` is diagonal. So
`Tr ∘ Δ^⊗ = α^⊗ + β^⊗` exactly, and

```text
HH(α ⊞ β) = HH(Φ) HH(Δ) = HH(Tr) HH(Δ) = HH(α) + HH(β).
```

## Step 4. Item 1

(S) says `σ = id ⊞ σ`. By Step 3, `HH(σ) = HH(id) + HH(σ)`, so `HH(id) = 0`, that is,
`HH_*(A) = 0`. For a unital `D`, the elements `1 ⊗ s_i`, `1 ⊗ s_i^*` and the endomorphism
`id_D ⊗ σ` form a swindle structure on `D ⊗ A`, since (S) is checked on elementary
tensors. So `HH_*(D ⊗ A) = 0`. Matrices follow from (I1). The same steps give
`HC_*(D ⊗ A) = 0`.

## Step 5. A swindle endomorphism of a nonzero algebra is never inner

Suppose `σ = Ad w` for a unit `w`. Put `t_1 = w^(-1) s_1`, `t_1^* = s_1^* w`,
`t_2 = w^(-1) s_2 w`, `t_2^* = w^(-1) s_2^* w`. These again satisfy the Cuntz relations,
and conjugating (S) by `w^(-1)` gives `a = t_1 a t_1^* + t_2 a t_2^*` for all `a`.
Multiplying by `t_1^*` on the left gives `t_1^* a = a t_1^*`. Multiplying by `t_1` on the
right gives `a t_1 = t_1 a`. So `t_1, t_1^*` are central, hence `t_1 t_1^* = t_1^* t_1 = 1`
and `t_2 t_2^* = 1 − t_1 t_1^* = 0`. Then `1 = (t_2^* t_2)^2 = t_2^* (t_2 t_2^*) t_2 = 0`,
so `A = 0`. No hypothesis on the centre is used.

## Step 6. Items 2 and 3

*Item 2.* Using only (S) and the Cuntz relations:
- `σ(a) s_1 = s_1 a` and `s_1^* σ(a) = a s_1^*`;
- `σ(a) s_2 = s_2 σ(a)` and `s_2^* σ(a) = σ(a) s_2^*`.

So `s_2, s_2^* ∈ R`. Also `e σ(a) = s_1 a s_1^* = σ(a) e`, so `e ∈ R` and `1 − e ∈ R`.
In `R`, `s_2^* s_2 = 1` and `s_2 s_2^* = 1 − e`. So `[1] = [e] + [1 − e] = [e] + [1]` in
`K_0(R)`, and `[e] = 0`.

*Item 3.* Let `v, v^* ∈ R` with `v^* v = 1`, and put `p = v v^*` with `e p = p`. Then
`e v = e p v = p v = v`. Set `u = s_1^* v` and `u^* = v^* s_1`.
- `u^* u = v^* e v = v^* v = 1`.
- `q := u u^* = s_1^* p s_1`.
- Since `v, v^* ∈ R`, `u σ(a) u^* = s_1^* σ(a) p s_1 = a s_1^* p s_1 = a q`.
- Also `u σ(a) u^* = s_1^* p σ(a) s_1 = s_1^* p s_1 a = q a`.

So `q` is a central idempotent. If `q = 0`, then `1 = (u^* u)^2 = u^* q u = 0`. So `q = 1`,
`u` is a unit with inverse `u^*`, and `σ(a) = u^* a u` is inner. This contradicts Step 5.

## Conditional corollaries (imports not quoted verbatim; not part of the ESTABLISHED statement)

- **(C1) Leavitt algebras.** Ara–Cortiñas (Proc. AMS 141 (2013), *Tensor products of
  Leavitt path algebras*) show `L_2 ⊗ L_2 ≇ L_2` through `HH_2(L_2 ⊗ L_2) ≠ 0 = HH_2(L_2)`.
  By Künneth, the first requires `HH_1(L_2) ≠ 0`. With item 1 this re-proves that `L_2` is
  not a swindle factor, and extends it to every tensor product of Leavitt path algebras
  whose Hochschild homology is nonzero. It uses no coefficient ring `k[ε]`.
- **(C2) Cantor crossed products by Poincaré duality groups.** For `C = LC(X,k)` and any
  action of `P`, the Hochschild complex of `C ⋊ P` splits over conjugacy classes of `P`.
  The class of `e` computes `H_*(P; C)`, because `C` is a directed union of the separable
  algebras `k^m` and so `HH_(>0)(C) = 0` (Feigin–Tsygan 1987; Nistor, Invent. Math. 99
  (1990)). If `P` is a `PD_d` group over `k` (orientation is automatic over `F_2`), then
  `H_d(P; C) ≅ H^0(P; C) ⊇ k·1 ≠ 0`. So:
  - no Cantor crossed product by `Z^d`, by a surface group, or by any closed aspherical
    manifold group is a swindle factor, whatever the action, free or not;
  - the same holds for its tensor products with anything of nonzero `HH`. This covers the
    Z^2-SFT hosts `B_Ω` and `B_Ω ⊗ L_∂`, the latter given (C1).
