---
rg: 2
id: symplectic-leavitt-swindle-proof
kind: route
title: The hyperbolic image of the elementary Leavitt matrix conjugates two commuting copies of Sp_2g(Z) onto one, so the class equals twice itself in H_2; a central extension with zero pulled-back class splits and a perfect group maps trivially to its kernel
target: leavitt-swindle-kills-deligne-center-in-ring-induced-hosts
requires:
  - deligne-lattice-is-universal-central-extension-for-g-ge-4
---

Notation as in the target. Blocks are `g × g`. Write `x_i^* = y_i`, so `y_i x_j = δ_ij`
and `x_1 y_1 + x_2 y_2 = 1`.

## Step 1. Three copies

Split `S^6g` into `L ⊕ L'`, with `L = L_1 ⊕ L_2 ⊕ L_3` the first `3g` coordinates and
`L' = L'_1 ⊕ L'_2 ⊕ L'_3` the last `3g`, and use the form `J_3g`. It suffices to take
`m = 3g`, because `A_m = j ∘ A_3g` for the standard stabilization `j`, and `j` maps
`Q_0(3g)` into `Q_0(m)`.

For `a = [[α, β], [γ, δ]] ∈ Sp_2g(Z)` and `k ∈ {1, 2, 3}`, let `a_k` act as `a` on
`L_k ⊕ L'_k` and as the identity elsewhere. Then `a_1 = A_3g(a)`. The three copies
commute, and `a ↦ a_k` is a homomorphism. For example `a_1 a_2` has blocks
`α̂ = diag(α, α, I)`, `β̂ = diag(β, β, 0)`, `γ̂ = diag(γ, γ, 0)` and `δ̂ = diag(δ, δ, I)`.

## Step 2. The Leavitt matrix is unitary and elementary

Let `𝒳 = (x_1 I, x_2 I)` (`g × 2g`) and `𝒴 = (y_1 I ; y_2 I)` (`2g × g`), so `𝒳𝒴 = I_g`
and `𝒴𝒳 = I_2g`. Put

```text
W = [[𝒴, 0], [0, 𝒳]]    (row blocks 2g, g; column blocks g, 2g).
```

**Unitary.** `W^* = [[𝒳, 0], [0, 𝒴]]` (row blocks `g, 2g`). `W^* W` is block diagonal with
`𝒴^* 𝒴 = x_1 y_1 + x_2 y_2 = I` and `𝒳^* 𝒳 = (y_i x_j) = I`, and `W W^* = I` in the same way.
So `W^* = W^-1`, and `H(W^*) = diag(W^*, W^*)`.

**Elementary** (the factorization of `leavitt-pair-centralizers-embed-e-n-in-st-3n-plus-1`,
re-derived). With the block unipotents
- `U_1 = [[I_2g, 0], [𝒳, I_g]]`,
- `U_2 = [[I_2g, -𝒴], [0, I_g]]`,
- `U_3 = [[I_g, -𝒳], [0, I_2g]]`,

we get `U_1 W = [[𝒴, 0], [I_g, 𝒳]]`, then `U_2 U_1 W = [[0, -I_2g], [I_g, 𝒳]]`, then
`U_2 U_1 W U_3 = [[0, -I_2g], [I_g, 0]] =: P_0`.
- `P_0` is a signed permutation matrix. Its permutation is `g` three-cycles, which is even,
  and it has `2g` signs, so `det P_0 = 1`.
- So `P_0 ∈ SL_3g(Z) = E_3g(Z)`, and `W ∈ E_3g(S)`.

Since `W^* = W^-1`, also `W^* ∈ E_3g(S)`. Put `U = H(W^*) ∈ H(E_3g(S)) ⊆ Q`.

## Step 3. Two conjugations

**`U (a_1 a_2) U^-1 = a_1`.** Integer entries commute with every `x_i, y_i`.
- The top-left block of `W^* α̂ W` is `x_1 α y_1 + x_2 α y_2 = α`.
- The lower-right block is `(y_i x_j) = I_2g`, and the off-diagonal blocks vanish. So
  `W^* α̂ W = diag(α, I, I)`.
- In the same way `W^* β̂ W = diag(β, 0, 0)`, `W^* γ̂ W = diag(γ, 0, 0)` and
  `W^* δ̂ W = diag(δ, I, I)`.

Since `U = diag(W^*, W^*)`, this is the claim.

**`P a_1 P^-1 = a_2`.** Let `π ∈ SL_3g(Z)` swap `L_1` and `L_2` and multiply `L_2` by `-1`
if `g` is odd. Put `P = H(π) ∈ H(E_3g(Z)) ⊆ Q`. The sign acts on `L_2 ⊕ L'_2` as `-1`,
which is central, so `P a_1 P^-1 = a_2`.

## Step 4. Homology (item 1)

Write `f(a) = a_1`, `f'(a) = a_2` and `F = f f'`, all homomorphisms `Sp_2g(Z) → Q`.
Inner automorphisms act trivially on `H_*(Q)`, so Step 3 gives `F_* = f_*` and `f'_* = f_*`.

`F` is `m ∘ (f × f') ∘ Δ`, where `Δ` is the diagonal and `m(u, v) = uv` is a homomorphism
on `f(G) × f'(G)`, because the images commute. `G = Sp_2g(Z)` is perfect for `g ≥ 3`
(standard). So Künneth gives `H_2(G × G) = H_2(G) ⊕ H_2(G)`: the `H_1 ⊗ H_1` and Tor
terms vanish. Also `Δ_* c = (c, c)`, and `m ∘ (f × f')` restricted to the two factors is
`f` and `f'`. Hence

```text
f_* c = F_* c = f_* c + f'_* c = 2 f_* c,
```

so `f_* c = 0`.

## Step 5. Central extensions (item 2)

Let `C = ker π`. The pullback `E_A = {(e, a) : π(e) = A(a)} → Sp_2g(Z)` is a central
extension by `C`, with class `A^*[E] ∈ H^2(Sp_2g(Z); C)`.
- By universal coefficients, `H^2(G; C) → Hom(H_2(G), C)` is natural, and it is an
  isomorphism for `G = Sp_2g(Z)`, since `Ext(H_1 G, C) = 0`.
- The class evaluates as `c ↦ ⟨[E], A_* c⟩ = 0` by Step 4. So `E_A ≅ C × Sp_2g(Z)` over
  `Sp_2g(Z)`.

Now `(Φ, p) : G' → E_A` is a homomorphism over `Sp_2g(Z)`. Its `C`-coordinate is a
homomorphism from a perfect group to an abelian group, hence trivial. So for `k ∈ K`,
`(Φ(k), 1)` corresponds to `(1, p(k)) = (1, 1)`, and `Φ(k) = 1`.

## Step 6. Items 3–5

**Item 3.** For `g ≥ 4`, `Γ~_g` is the universal central extension of the perfect group
`Sp_2g(Z)` (`deligne-lattice-is-universal-central-extension-for-g-ge-4`), hence perfect. For the lower-rank clause,
`σ Φ'` lifts `A_m p` into `E`, so item 2 gives `σ Φ'(K) = 1`.

**Item 4.** The involution of `R_L`. The anti-endomorphism of the free ring fixed by
`s_i ↦ t_i`, `t_i ↦ s_i`, `N ↦ N`, `A ↦ A` sends each relator into the relator ideal:
- `(t_i s_j − δ_ij)^* = t_j s_i − δ_ij` and `(s_1 t_1 + s_2 t_2 − 1)^* = s_1 t_1 + s_2 t_2 − 1`;
- the two `A`-relators are swapped;
- `(N s_1 − s_1(N+1))^* = t_1 N − (N+1) t_1`, and in `R_L`,
  `t_1 N = t_1 N (s_1 t_1 + s_2 t_2) = t_1 s_1 (N+1) t_1 + t_1 (N s_2) t_2 = (N+1) t_1`;
- `(N s_2)^* = t_2 N`, and `t_2 N = t_2 s_1 (N+1) t_1 + t_2 (N s_2) t_2 = 0`.

So `*` descends to `R_L`. It squares to the identity on generators, so it is an
involution, and `(s_1, s_2)` is a `*`-Leavitt pair.

**Item 5.** Repeat Steps 1–4 with `a ↦ a_k` acting on `L_k` only. This uses `W^*` itself
in place of `H(W^*)` and `π` in place of `H(π)`, and needs no involution.
