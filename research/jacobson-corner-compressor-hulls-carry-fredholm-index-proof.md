---
rg: 2
id: jacobson-corner-compressor-hulls-carry-fredholm-index-proof
kind: route
title: Compressors push the moved module into itself and the fixed module outward, the corner block is Toeplitz-Fredholm, and the relative index is additive
target: jacobson-corner-compressor-hulls-carry-fredholm-index
requires:
  - jacobson-elementary-subgroups-are-locally-finite-by-linear
---

Notation as in the target. `F` is any field here. `e_ab = S^a Q T^b` with `Q = 1 - ST`. These
satisfy `e_ab e_cd = delta_bc e_ad`, span `I`, and act on `F^(N)` as matrix units, so every
element of `M_m(I)` acts on `F^(N) (x) F^m` with finite rank. `J / I = F[x,x^-1]`
(Step 5 of `compression-criterion-inert-on-modular-linear-extensions-proof`). Write
`L_1 = GL_m(J, I)` for the kernel of `rho` on `GL_m(J)`. Its elements are the automorphisms
`1 + A` of `V_1` with `A` a finite matrix in the standard basis, so `L_1` is the union of the
groups `GL` of finite coordinate blocks. `SL_fin(V_1)` denotes the union of the corresponding
groups `SL`. This is the meaning of `SL_fin(V_1)` in the target.

## Step 0. Two facts about corners

**(0a) `SL_fin(V_1) <= E_m(J)`.** Index the basis of `V_1` by pairs `(a, i)`, with `a` in `N` and
`1 <= i <= m`. The elementary transvection `t_((a,i),(b,j))(lambda)` with `i != j` is the elementary
matrix `x_ij(lambda e_ab)`. For `i = j` and `a != b`, pick `k != i` and use the commutator identity
`[t_xy(1), t_yz(lambda)] = t_xz(lambda)` for distinct basis indices `x != z`, with `y = (0, k)`.
Transvections generate `SL_fin(V_1)`, the union of the groups `SL` of finite coordinate blocks.

**(0b) `E_m(J)` is normal in `GL_m(J)` for `m >= 3`.**
- `F[x,x^-1]` is Euclidean, so `rho(E_m(J)) = E_m(F[x,x^-1]) = SL_m(F[x,x^-1])`, which is normal.
- Let `k in GL_m(J)`. Then `rho(k E_m(J) k^-1) <= SL_m`, so `k E_m(J) k^-1 <= E_m(J) L_1`.
- `E_m(J)` is perfect for `m >= 3`, since `x_ij(a) = [x_ik(a), x_kj(1)]`. So `k E_m(J) k^-1`
  lies in the derived subgroup of `E_m(J) L_1`.
- `E_m(J)` normalizes `L_1`. The determinant of a finitary automorphism is invariant under
  conjugation by any automorphism of `V_1`. So `[E_m(J), L_1]` and `[L_1, L_1]` lie in
  `SL_fin(V_1)`, which lies in `E_m(J)` by (0a). Hence the derived subgroup of `E_m(J) L_1` lies
  in `E_m(J)`.
- So `k E_m(J) k^-1 <= E_m(J)`. Apply this to `k^-1` for equality.

(0b) is needed only for the example `E_m(J) + 1`. A general corner has `Gamma_1` normal in
`GL_m(J)` by definition.

**(0c) Moved and fixed modules.** Put `Mov(Gamma) = span{(gamma - 1)v}` and
`Fix(Gamma) = {v : gamma v = v for all gamma}`. For a corner, `Mov(Gamma) = V_1` and
`Fix(Gamma) = V_2`.
- `Gamma` acts as the identity on `V_2` and preserves `V_1`. So `Mov <= V_1` and `Fix >= V_2`.
- `SL_fin(V_1) <= Gamma_1` moves every basis vector of `V_1`, so `Mov = V_1`.
- `SL_fin(V_1)` fixes no nonzero vector of `V_1`, so `Fix = V_2`.

## Step 1. Compressors push `V_1` in and `V_2` out (Theorem part 1, first half)

Let `g Gamma g^-1 <= Gamma`. For every `gamma`, `(g gamma g^-1 - 1) V = g (gamma - 1) V`, so
`Mov(g Gamma g^-1) = g Mov(Gamma)` and `Fix(g Gamma g^-1) = g Fix(Gamma)`. A subgroup moves less
and fixes more, so by (0c)

```text
g V_1 <= V_1,        g V_2 >= V_2.                               (C1)
```

## Step 2. The corner block is Fredholm (Theorem part 1, second half)

Write `g` in blocks `[[g_11, g_12], [g_21, g_22]]` for `V = V_1 + V_2`. By (C1), `g_21 = 0`, so
`g V_1 = g_11 V_1`, and `g_11` is injective on `V_1` because `g` is.
- `rho(g)` is block upper triangular, and its determinant is a unit of `F[x,x^-1]`. So
  `A = rho(g_11)` has unit determinant and lies in `GL_m(F[x,x^-1])`.
- Lift `A^-1` entrywise to `h in M_m(J)`. Then `g_11 h - 1` lies in `M_m(I)` and has finite rank.
  Call it `R`.
- `g_11 V_1` contains `(1 + R) V_1`, which contains `ker R`, a subspace of finite codimension.

So `c(g) = dim V_1 / g V_1` is finite.

## Step 3. Index zero means normalizing (Theorem part 2)

If `g Gamma g^-1 = Gamma`, the same argument applied to `g^-1` gives `g^-1 V_1 <= V_1`, so
`g V_1 = V_1` and `c(g) = 0`.

Conversely, let `c(g) = 0`, so `g V_1 = V_1`. Then `V = g V_1 + g V_2 = V_1 + g V_2` is direct.
Since `V_2 <= g V_2` by (C1), the modular law gives `g V_2 = V_2 + (g V_2 cap V_1) = V_2`.
- So `g = diag(g_1, g_2)` is block diagonal.
- `g_1` is invertible on `V_1` with inverse the `(1,1)` block of `g^-1`, so `g_1 in GL_m(J)`.
- Hence `g Gamma g^-1 = g_1 Gamma_1 g_1^-1 + 1 = Gamma`, because `Gamma_1` is normal in
  `GL_m(J)`.

## Step 4. The relative index is a homomorphism on the hull (Theorem part 3)

Call subspaces `A, B` of `V` commensurable when `A/(A cap B)` and `B/(A cap B)` are finite
dimensional, and put `[A : B] = dim A/(A cap B) - dim B/(A cap B)`. Standard linear algebra gives:
- `[A : C] = [A : B] + [B : C]` for pairwise commensurable `A, B, C`;
- `[kA : kB] = [A : B]` for every linear automorphism `k`.

By Steps 1 and 2, every compressor `g` of `Gamma` in `GL_N(J)` has `g V_1 <= V_1` of finite
codimension, so `g` and `g^-1` commensurate `V_1`. Products of elements commensurating `V_1`
commensurate it, since `h k V_1` is commensurable with `h V_1`, which is commensurable with `V_1`.
So the whole group `D_H` generated by the compressors in `H` commensurates `V_1`. For `h, k` in
`D_H`,

```text
ind(hk) = [V_1 : hk V_1] = [V_1 : h V_1] + [h V_1 : hk V_1] = ind(h) + ind(k),
```

and `ind(g) = c(g) >= 0` on compressors. This proves the Theorem.

## Step 5. The corollaries

**FI-normal.** If `D_G` has no nonzero homomorphism to `Z`, then `ind = 0` on `D_G`. So `c(g) = 0`
for every compressor, and Step 3 shows that every compressor normalizes `Gamma`. If `Gamma` is
infranormal in `G`, then `D_G = G`, and so `G = N_G(Gamma)`. A Kazhdan group has finite
abelianization, hence no nonzero homomorphism to `Z`.

**FI-DD.** Let `Gamma <= G <= H <= GL_N(J)` with `G` Kazhdan and `Gamma` an infranormal corner.
By FI-normal, `Gamma` is normal in `G`. For `z` in `C_H(Gamma)` and `g` in `G`, `g z g^-1`
centralizes `g Gamma g^-1 = Gamma`. So the rigid defect `[g z g^-1, gamma]` is trivial for every
choice. A `GL_N(J)`-conjugate corner `k Gamma k^-1` reduces to this case by conjugating `H` by
`k^-1`, which replaces `V_1` by `k V_1`.

## Step 6. The closing-remark compressor

In `GL_(2m)(J)`, `u = [[S, Q], [0, T]]` (each entry times `1_m`) has `u^-1 = [[T, 0], [Q, S]]`. It
compresses `E_m(J) + 1`, and `u V_1 = S V_1`. `S` has cokernel spanned by `e_0` on `F^(N)`, so
`ind(u) = c(u) = m`. This is the same character, read as a Fredholm index, as the top-block
determinant `x^m` of `compression-criterion-inert-on-modular-linear-extensions-proof`.

## Checks

- (C1) uses only `Mov(Gamma) = V_1` and `Fix(Gamma) = V_2`.
- Step 2 uses only that `g` lies in `GL_N(J)`. For a general automorphism of `V`, `c(g)` can be
  infinite. This is exactly why the Leavitt compressors escape.
- Step 3 is the only place where normality of `Gamma_1` in `GL_m(J)` is used.
