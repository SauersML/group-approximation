---
rg: 2
id: extension-product-closures-cannot-create-sl-n-q-proof
title: Direct proof of: extension product closures cannot create sl n q
kind: route
title: Direct proof by tracking the nontrivial images of SL_n(Q)
target: extension-product-closures-cannot-create-sl-n-q
requires: []
---

Direct proof. Not independently reviewed. Fix `n >= 2` and write `S = SL_n(Q)`,
`Z = Z(S)`, which is `{±I}` for `n` even and trivial for `n` odd.

## Step 0. The nontrivial images of S

`PSL_n(K)` is simple for every field `K` with more than three elements and every
`n >= 2`, and `SL_n(K)` is perfect in that range. Let `N` be normal in `S`. Its
image in `PSL_n(Q)` is trivial or everything. In the second case `NZ = S`, and
then `S = [S,S] = [NZ,NZ] = [N,N] <= N`. So every normal subgroup of `S` is
central or all of `S`. Hence every nontrivial homomorphic image of `S` is
isomorphic to `S` or to `S/Z = PSL_n(Q)`. This proves the equivalence in the
definition of `P_n`: a group lies in `P_n` exactly when it has no subgroup
isomorphic to `SL_n(Q)` or `PSL_n(Q)`.

## Step 1. Seeds

Let `L = S/C` with `C <= Z`, and write `e(x)` for the elementary matrix with
`(1,2)` entry `x`. Put `d = diag(2, 1/2, 1, ..., 1)`.
- `U = {e(x) : x in Q}` is isomorphic to `(Q,+)`.
- `d e(x) d^-1 = e(4x)`, so `B = <e(1), d> = {e(x) d^k : x in Z[1/2], k in Z}` is
  isomorphic to `Z[1/2] x|_(x4) Z`. This is `BS(1,4) = <a, t | t a t^-1 = a^4>`,
  since `BS(1,4)` is isomorphic to `Z[1/4] x|_(x4) Z` and `Z[1/4] = Z[1/2]`.
- Every element of `U` or `B` has diagonal `(2^k, 2^-k, 1, ..., 1)`. So neither
  meets `Z` except in `I`, and both embed in `L`.

So every nontrivial image of `S` contains `(Q,+)` and `BS(1,4)`, and a group that
lacks either one lies in `P_n`. The listed memberships:
- **Residually finite groups.** `(Q,+)` is divisible, so its image in a finite
  quotient is a finite divisible group, which is trivial. A residually finite
  group therefore contains no `(Q,+)`.
- **Solvable groups.** The image of the perfect group `S` is perfect and
  solvable, so it is trivial.
- **Groups whose abelian subgroups are finitely generated.** These contain no
  `(Q,+)`.
- **`V` and `T`.** Neither contains `(Q,+)` (survey arXiv:2306.16356v3, Theorem
  4.4: "In particular, Q does not embed into V").
- **`VA`, `T-bar` and `A`.** In `BS(1,4)`, `a^(4^k) = t^k a t^-k` has word length
  at most `2k+1`, so `<a>` is distorted. Burillo--Felipe, arXiv:2605.09763v1,
  Corollary 5: "VA does not contain any group with cyclic subgroups that are
  distorted." So `BS(1,4)` embeds in no subgroup of `VA`.

## Step 2. Closure

Let `f : S -> K` be a homomorphism.
- **Subgroups.** Immediate.
- **Extensions.** Let `N` be normal in `K` with `N` and `K/N` in `P_n`. The
  composite `S -> K/N` is trivial, so `f(S) <= N`, and then `f` is trivial.
- **Direct products.** Suppose `K` is contained in `prod_i H_i` (restricted or
  unrestricted) with each `H_i` in `P_n`. Every coordinate of `f` is trivial,
  so `f` is trivial.
- **Free products.** Suppose `K = *_i H_i` with each `H_i` in `P_n` and `f`
  nontrivial. Then `L = f(S)` is `SL_n(Q)` or `PSL_n(Q)`, by Step 0. By Kurosh,
  `L = F * (*_j g_j L_j g_j^-1)` with `F` free and each `L_j` inside some `H_i`.
  - `L` is not free, because it contains `(Q,+)`.
  - `L` is not a free product of two nontrivial groups.
    - A free product of two nontrivial groups has trivial centre, so `L` is not
      `SL_n(Q)` for `n` even.
    - Otherwise `L` is simple. A nontrivial free product `X * Y` is not simple,
      since the normal closure of `Y` is the kernel of `X * Y -> X`.

  So `L` is a single conjugate `g L_j g^-1` inside some `g H_i g^-1`. That gives
  a nontrivial homomorphism `S -> H_i`, a contradiction.
- **Derived operations.**
  - A semidirect product `N x| G` is an extension.
  - A restricted or unrestricted permutational wreath product `A wr_X G` is an
    extension of `A^(X)` or `A^X` by `G`, and both are products.
  - If `H <= K` has finite index, then `K` is an extension of the core of `H`, a
    subgroup of `H`, by a finite group. Finite groups contain no `(Q,+)`.

## Step 3. Consequence

If every member of `C` lies in `P_n`, then by transfinite induction on the
construction every member of `Cl(C)` does too, by Step 2. `GL_n(Q)` contains
`SL_n(Q)`, so neither of them embeds in a member of `Cl(C)`. Taking the
contrapositive gives item 3 of the claim.

## Step 4. Sharpness

Each `SL_n(Z[1/m!])` is a finitely generated linear group, so it is residually
finite (Mal'cev) and lies in `P_n` by Step 1. Their directed union is `S`, which
is not in `P_n`. The fundamental group of the ray of groups
`G_1 <= G_2 <= ...`, with the inclusions as edge maps, is the direct limit
`union_k G_k`. So `P_n` is not closed under graphs of groups over infinite
graphs either.
