---
rg: 2
id: q-free-normal-towers-omit-aff-q-proof
kind: route
title: Direct proof with Higman's theorem as the only outside input
target: q-free-normal-towers-omit-aff-q
requires: []
---

Direct proof. Not independently reviewed. Notation as in
`q-free-normal-towers-omit-aff-q`. The only outside input is Higman's theorem
that `V` contains no copy of `(Q,+)` (survey arXiv:2306.16356v3, Theorem 4.4:
"In particular, Q does not embed into V").

## Step 0. Quotients of Q

A quotient of `(Q,+)` by a nonzero subgroup `A` is a torsion group. Take
`a ∈ A` nonzero and `q ∈ Q`, and write `q/a = m/k` with `k >= 1`. Then
`kq = ma ∈ A`. So every quotient of `Q` is either `Q` itself or torsion.

## Step 1. Closure

- **Subgroups.** For `H <= E` put `H_i = H ∩ E_i`. Each is normal in `H`, and
  `H_i/H_{i+1}` embeds in `E_i/E_{i+1}`.
- **Finite products.** For `E, F ∈ 𝒯` with chains `(E_i)`, `(F_j)`, the chain
  `E_i × F` (`i = 0..r`) followed by `1 × F_j` consists of normal subgroups of
  `E × F`, with factors `E_i/E_{i+1}` and `F_j/F_{j+1}`.
- **Q-free kernels.** If `K` is Q-free and normal and `E/K` has the chain
  `(F_i)`, take the preimages of the `F_i`, then `K`, then `1`.
- **`LC(C,H)` is Q-free if `H` is.** Let `D ≅ Q` lie in `LC(C,H)` and let
  `d ∈ D`. For `x ∈ C`, evaluation `ev_x : LC(C,H) -> H` is a homomorphism, so
  `ev_x(D)` is a divisible quotient of `Q` inside the Q-free group `H`. By
  Step 0 it is torsion, so `d(x)` has finite order. Since `d` takes finitely
  many values, `d` has finite order. `D` is torsion-free, so `d = 1`. Hence
  `D = 1`, a contradiction.
- **Continuous wreath.** Let `H ∈ 𝒯` with chain `(H_i)`, and let
  `E = LC(C,H) ⋊ V`. Put `E_0 = E` and `E_{i+1} = LC(C, H_i)`.
  - Each `LC(C,H_i)` is normal in `LC(C,H)` pointwise, and invariant under
    precomposition by `V`, so it is normal in `E`.
  - `E/E_1 ≅ V` is Q-free (Higman).
  - `E_{i+1}/E_{i+2} ≅ LC(C, H_i/H_{i+1})`. Reduction mod `H_{i+1}` is onto,
    because a locally constant map takes finitely many values on a clopen
    partition, and each value lifts. Its kernel is `LC(C, H_{i+1})`. This
    quotient is Q-free by the previous item.

## Step 2. Exclusion

**Lemma.** There is no configuration `A <= E ∈ 𝒯`, `T ⊴ A`, `T ≅ (Q,+)`, in
which the conjugation action of `A` on `T` includes multiplication by `t^2` for
every `t ∈ Q^x`.

*Proof.* We show by induction that `T <= E_i` for every `i`, which contradicts
`E_r = 1`.
1. `T <= E_0 = E`.
2. Suppose `T <= E_i`. Then `T/(T ∩ E_{i+1})` embeds in the Q-free group
   `E_i/E_{i+1}`, so `B = T ∩ E_{i+1}` is nonzero.
3. `E_{i+1}` is normal in `E`, so `B` is invariant under conjugation by `A`.
   Hence `B` is a nonzero subgroup of `Q` closed under multiplication by every
   rational square.
4. For `b ∈ B` nonzero and any `q ∈ Q`, put `u = q/b`. Then
   `q = b((u+1)/2)^2 - b((u-1)/2)^2 ∈ B`, so `B = T` and `T <= E_{i+1}`.

**Applications.**
- **`Aff(Q)`.** Take `T` to be the translations. Conjugation by `x ↦ ax` is
  multiplication by `a`, which includes all squares.
- **`B_2(Q)`.** Take `T = {[[1,b],[0,1]]}`. Conjugation by `diag(t, t^-1)` is
  multiplication by `t^2`.
- **The image of `B_2(Q)` in `PSL_2(Q)`.** `T ∩ {±1} = 1`, so `T` maps
  isomorphically, and the torus acts in the same way.
- **`GL_n(Q)`, `n >= 2`.** It contains `Aff(Q)` as the matrices
  `diag([[a,b],[0,1]], I_(n-2))`.
- **`SL_n(Q)`.** It contains `B_2(Q)` in the upper-left block.
- **`PGL_n(Q)`.** The same `Aff(Q)` block maps injectively, since such a matrix
  is scalar only when `a = 1` and `b = 0`.
- **`PSL_n(Q)`.** Take the `B_2(Q)` block. The unipotents are not scalar, so `T`
  maps isomorphically. `diag(t, t^-1, 1, ..., 1)` acts on `T` by `t^2`.

## Step 3. Sharpness

- **`(Q,+)`.** `Z` is normal, `Q/Z` is torsion hence Q-free, and `Z` is Q-free.
- **`U_3(Q)`.** Conjugation acts trivially on `U_3(Q)/Z(U_3(Q)) ≅ Q^2`. So
  `U_1`, the preimage of `Z^2`, is normal. `U_2 = e_13(Z)` is central, hence
  normal. The factors:
  - `U_3(Q)/U_1 ≅ (Q/Z)^2` is torsion.
  - `U_1/U_2` is Q-free. A copy of `Q` in it has divisible image in `Z^2`,
    hence trivial image, so it lies in the torsion centre `e_13(Q)/e_13(Z) ≅ Q/Z`,
    which is impossible.
  - `U_2 ≅ Z`.

  All three factors are Q-free, and all terms are normal in `U_3(Q)`.
