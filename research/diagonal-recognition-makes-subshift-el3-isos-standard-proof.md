---
rg: 2
id: diagonal-recognition-makes-subshift-el3-isos-standard-proof
kind: route
title: Pointwise automorphisms of the diagonal, roots as double centralizers of their locally constant parts, and no mixed orientation over a simple ring
target: diagonal-recognition-makes-subshift-el3-isos-standard
requires:
  - locally-constant-simple-group-normal-subgroups-are-open-sets
  - subshift-elementary-group-rigid-supports-are-mutual-centralizers
  - el3-root-subgroups-are-bicommutant-closed
  - peirce-root-homomorphisms-of-e3-are-standard
  - minimal-subshift-algebra-is-simple-lef-ring
  - cantor-crossed-product-matrix-ring-iso-forces-soe
artifacts:
  - research/artifacts/sk-iso-rigidity-2026-09-13-part2.md
---

Notation: `Q = GL_3(F_2)`, `D_X = LC(X,F_2)`, `L = L_X = GL_3(D_X) = LC(X,Q)`, `L′ = GL_3(B) = LC(Ω,Q)`. Replacing `α` by
`inn(h^{-1})∘α` we may assume `α(L) = L′`. For `U` clopen and `c ∈ Q`, `c_U` denotes the function equal to `c` on `U`
and to `1` elsewhere.

**Step 1 (pointwise form).** There are a homeomorphism `η: X → Ω` and a locally constant `β: Ω → Aut(Q)` with
`α(f)(ω) = β_ω(f(η^{-1}ω))` for all `f ∈ L`.
- By `locally-constant-simple-group-normal-subgroups-are-open-sets` (`Q` is simple nonabelian of order 168), `α` maps
  `N_O = {f : supp f ⊆ O}` onto `N_{η(O)}` for a homeomorphism `η`.
- `supp f` is the smallest open `O` with `f ∈ N_O`, so `supp α(f) = η(supp f)`.
- For `U = U_1 ⊔ U_2`, `c_U = c_{U_1}c_{U_2}`, and `α(c_{U_1})` is supported in `η(U_1)`. So on `η(U_1)`, `α(c_U)` agrees with
  `α(c_{U_1})`.
- Put `β_ω(c) = α(c_U)(ω)` for any clopen `U ∋ η^{-1}ω`. By the previous point this does not depend on `U`.
- `β_ω` is a homomorphism. It is injective because `ω ∈ supp α(c_U)` when `c ≠ 1`.
- `β_ω(c) = α(c_X)(ω)` is locally constant in `ω`, and `Q` is finite.
- A general `f` is a product of `c_U`'s over a clopen partition, which gives the formula.

**Step 2 (normalization).** `Aut(Q) = Inn(Q) ⋊ ⟨γ_0⟩` with `γ_0(g) = (g^t)^{-1}`. This is Steinberg's description of
automorphisms of `SL_3` over a prime field (diagonal and field automorphisms trivial, one graph automorphism, and
`|Out(L_3(2))| = 2`); recalled, not source-checked here.
- On a clopen partition where `β` is constant, write `β_ω = inn(g_ω)∘γ_0^{ε(ω)}`.
- The element `g = (ω ↦ g_ω)` lies in `L′ ⊆ G_Y`, and `inn(g^{-1})∘α` has `β_ω = γ_0^{ε(ω)}`.
- Put `p = 1_{ε=0}` and `q = 1_{ε=1}`. These lie in `B`, with `p + q = 1` and `pq = 0`.

**Step 3 (roots from locally constant parts).** For a subset `S ⊆ R_Y` containing `1`, write `T_12(S) = {e_12(s) : s ∈ S}`.
- *A computation.* Suppose `g ∈ GL_3(R_Y)` commutes with `T_12(S)`.
  - For `s ∈ S`: `g_p1 s = 0` for `p ≠ 1`, `s g_2q = 0` for `q ≠ 2`, and `g_11 s = s g_22`.
  - With `s = 1`: `g_21 = g_31 = g_23 = 0` and `g_11 = g_22 =: c`, and `c` commutes with `S`.
- *For `S = Idem(B)`.*
  - `c ∈ C_{R_Y}(B) = B`.
  - `c` is a unit, and its inverse also commutes with `B`, so `c ∈ B^× = LC(Ω,F_2^×) = {1}`.
  - So `C_{G_Y}(T_12(B)) = C_{G_Y}(A_12(R_Y))`, the group of Lemma 1.1 of `el3-root-subgroups-are-bicommutant-closed`.
  - Then `C_{G_Y}(C_{G_Y}(T_12(B))) = A_12(R_Y)` by that node.
- *For `S = Idem(D_X)` in `G_X`.* The same holds since `D_X` is maximal commutative in `R_X`. So
  `C_{G_X}(C_{G_X}(A_12 ∩ L)) = A_12(R_X)`.
- Permuting indices gives every pair `i ≠ j`. `α` preserves centralizers, so

  `α(A_ij(R_X)) = C_{G_Y}(C_{G_Y}(α(A_ij ∩ L)))`.

**Step 4 (the images of the locally constant roots).**
- `A_ij ∩ L = {e_ij(f) : f ∈ D_X}`.
- Pointwise `γ_0(I + E_ij) = (I + E_ji)^{-1} = I + E_ji` in characteristic 2.
- So `α(A_ij ∩ L) = {I + bpE_ij + bqE_ji : b ∈ B}`.

**Step 5 (cases).**
- **(i) `q = 0`.**
  - By Steps 3–4, `α(A_ij(R_X)) = A_ij(R_Y)` for all `i ≠ j`.
  - `peirce-root-homomorphisms-of-e3-are-standard` with `E_k = E_kk` gives a ring isomorphism `Θ` with `α = Θ|_{G_X}`.
- **(ii) `p = 0`.**
  - The graph automorphism `γ_X(g) = (g*)^{-1}` of `G_X` fixes `L` setwise, since `τ|_{D_X} = id`, and acts pointwise as
    `γ_0`.
  - So `α∘γ_X` is in case (i), which gives the second form.
- **(iii) `p ≠ 0 ≠ q`. Impossible.**
  - Let `W_ij = pI + qP_(ij) ∈ L′`, where `P_(ij)` is the transposition matrix. Then `W_ij² = I`, and `B`-scalars commute with
    constant matrices.
  - Compute `W_ij(bpE_ij + bqE_ji)W_ij = bpE_ij + bqP_(ij)E_jiP_(ij) = bE_ij`. So `W_ij α(A_ij ∩ L) W_ij = T_ij(B)`, and by Step 3,
    `α(A_ij(R_X)) = M_ij := W_ij A_ij(R_Y) W_ij`.
  - `M_13` consists of `I + pxpE_13 + pxqE_11 + qxpE_33 + qxqE_31`, so every element of `M_13` has `(1,2)`-entry `0`.
  - Take `X_0 = W_12E_12W_12 = pE_12 + qE_21` and, for `s ∈ R_Y`, `Z_0 = W_23(sE_23)W_23 = pspE_23 + psqE_22 + qspE_33 + qsqE_32`.
  - Both square to `0`. In characteristic 2,
    `[I+X_0, I+Z_0] = I + X_0Z_0 + Z_0X_0 + X_0Z_0X_0 + Z_0X_0Z_0 + X_0Z_0X_0Z_0`.
  - The `(1,2)`-entries of the terms are `p·psq`, `0` (row 1 of `Z_0` is zero), `(X_0Z_0)_11·p = 0`, `0`, and `0`.
    So the commutator has `(1,2)`-entry `psq`.
  - `R_Y` is simple (`minimal-subshift-algebra-is-simple-lef-ring`), so `pR_Yq ≠ 0`. Choose `s` with `psq ≠ 0`.
  - But `[A_12, A_23] ⊆ A_13`, so `[M_12, M_23] ⊆ M_13`, a contradiction.

**Step 6.** In both surviving cases `M_3(R_X) ≅ M_3(R_Y)`. `cantor-crossed-product-matrix-ring-iso-forces-soe` with
`m = 3` gives strong orbit equivalence.

**Model tests.**
- `X = Y`, `α = id`: case (i).
- `α = γ_X`: case (ii).
- `α = ` conjugation by `W_12`: `β` is inner everywhere, so after Step 2 we are in case (i); the orientation is not
  mixed.
- *Simplicity is essential in (iii).* For a product ring `R = R_1 × R_2` with `p = (1,0)` central, the map equal to the
  identity on `E_3(R_1)` and to the graph automorphism on `E_3(R_2)` is a non-standard automorphism. The obstruction
  vanishes there because `psq = spq = 0` for every `s`.
