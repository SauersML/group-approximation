---
rg: 2
id: finite-image-higman-models-collapse-opnorm-proof
kind: route
title: Zassenhaus contraction plus Clifford permutation collapse finite-image models
target: finite-image-higman-models-collapse-opnorm
requires: [higman-group-embeds-in-no-almost-automorphism-group]
artifacts:
  - experiments/finite-image-collapse-2026-09-17/check_finite_image_collapse.py
---

Notation as in the target.  `G = <X | R>` has no nontrivial finite quotient.
The unitaries `u_x` in `U(V)`, with `V = C^k`, generate a finite group
`Gamma`.  Put `w_r = r(u)` and `delta = max_r ||w_r - 1|| < 1/2`.  All
norms are operator norms.

## Step 0: two elementary estimates

(E1) For unitaries `s, t`, `||[s,t] - 1|| = ||st - ts||`.  Also
`st - ts = (s-1)(t-1) - (t-1)(s-1)`.  Hence
`||[s,t] - 1|| <= 2 ||s-1|| ||t-1||`.

(E2) For unitaries `a, b`, `||ab - 1|| <= ||a-1|| + ||b-1||`, and
`||a^(-1) - 1|| = ||a - 1||`.

## Step 1: small elements generate a nilpotent normal subgroup

Let `S = {g in Gamma : ||g - 1|| <= delta}`.  It is symmetric and stable
under conjugation by `Gamma`, since conjugation by a unitary preserves
`||g - 1||`.  So `M = <S>` is normal in `Gamma`.

Define `T_1 = S` and `T_(j+1) = {[s,t] : s in S, t in T_j}`.  Each `T_j` is
`Gamma`-conjugation stable.  By (E1) and induction, every element of `T_j`
has distance at most `d_j = (2 delta)^(j-1) delta` from `1`.

Claim: `gamma_j(M)` is contained in `<T_j>`.  For `j = 1` this is the
definition.  Suppose it holds for `j`.  The subgroup `N = <T_(j+1)>` is
normal in `Gamma`, because `T_(j+1)` is conjugation stable.  In
`Gamma / N`, every element of `S` commutes with every element of `T_j`.
Hence the image of `M = <S>` commutes with the image of `<T_j>`.  So
`[M, <T_j>]` is contained in `N`, and therefore

```text
gamma_(j+1)(M) = [M, gamma_j(M)]  is contained in  [M, <T_j>],
```

which is contained in `N = <T_(j+1)>`.

The group `Gamma` is finite, so `m = min_(g != 1) ||g - 1|| > 0`.  Since
`2 delta < 1`, we have `d_J < m` for some `J`.  Then `T_J` is contained in
`{1}`, so `gamma_J(M) = 1`, and **`M` is nilpotent.**

## Step 2: the whole image is nilpotent

Each `w_r` lies in `S`, so it lies in `M`.  In the finite group
`Gamma / M`, the images of the `u_x` therefore satisfy every relator.  This
gives a homomorphism `G -> Gamma / M`, which is onto because the `u_x`
generate `Gamma`.  The group `G` has no nontrivial finite quotient, so
`Gamma = M`.  Hence **`Gamma` is nilpotent.**

## Step 3: reduction to an irreducible summand

The representation of the finite group `Gamma` on `V` splits as an
orthogonal direct sum `V = V_1 + ... + V_m` of irreducible invariant
subspaces, because the orthogonal complement of an invariant subspace is
invariant under a group of unitaries.  Every `u_x` and every `w_r` is block
diagonal, and the operator norm of a block-diagonal operator is the maximum
over its blocks.  So it suffices to prove, for each block `W = V_l`, that

```text
||u_x|_W - 1|| <= C_G max_r ||w_r|_W - 1||.
```

Let `Gamma_W` be the image of `Gamma` in `U(W)`.  It is a quotient of
`Gamma`, so it is finite and, by Step 2, nilpotent.  It acts irreducibly on
`W`, and the restricted defects are at most `delta`.

## Step 4: Clifford permutation forces the image to be abelian

Suppose `Gamma_W` is not abelian.  Its centre `Z` is proper.  The quotient
`Gamma_W / Z` is a nontrivial nilpotent group, so it has nontrivial centre
`Z_2 / Z`.  Pick `a` in `Z_2` but not in `Z`, and let `A = <Z, a>`.  Then
`A` is abelian, since `a` commutes with `Z`.  It is normal, since
`g a g^(-1)` lies in `a Z`, which is inside `A`.  It is not central, since
`a` is not in `Z`.

The finite abelian group `A` of unitaries gives an orthogonal decomposition
`W = sum over chi in Y of W_chi`.  Here `Y` is the set of characters `chi`
of `A` whose joint eigenspace `W_chi = {v : a v = chi(a) v for all a in A}`
is nonzero.  For `g` in `Gamma_W` we have `g W_chi = W_(chi^g)`, where
`chi^g(a) = chi(g^(-1) a g)`.  This gives a homomorphism
`pi : Gamma_W -> Sym(Y)`.  If `Y` had a single element, `A` would act by
scalars and so would be central.  Hence `|Y| >= 2`.  For any `chi`, the sum
of the `W_(chi^g)` is a nonzero invariant subspace, hence equal to `W`.  So
`pi` is transitive, and in particular nontrivial.

Now take a defect element `w = w_r|_W`, with `||w - 1|| <= delta < sqrt(2)`.
If `pi(w)` moved some `chi` to `psi != chi`, then a unit vector `v` in
`W_chi` would have `w v` in the orthogonal space `W_psi`, so that
`||w v - v|| = sqrt(2)`.  That is impossible.  So `pi(w_r) = 1` for every
relator.  Then `x -> pi(u_x|_W)` defines a homomorphism from `G` to the
finite group `Sym(Y)`, which is trivial.  The generators generate
`Gamma_W`, so `pi` is trivial, which is a contradiction.  **Therefore
`Gamma_W` is abelian.**

## Step 5: the abelian case and the constant

`Gamma_W` is abelian and irreducible, so `dim W = 1` and each `u_x|_W` is a
scalar `lambda_x` in the unit circle.  Each relator evaluates to
`r(lambda) = prod_x lambda_x^(E_(r,x))`.  Using `e_x = sum_r c_(r,x) E_r`,

```text
lambda_x = prod_r r(lambda)^(c_(r,x)),
```

and (E2) gives
`|lambda_x - 1| <= sum_r |c_(r,x)| |r(lambda) - 1| <= C_G max_r ||w_r|_W - 1||`.
Taking the maximum over the blocks proves (FIC).

For Higman, `r_i = g_i g_(i+1) g_i^(-1) g_(i+1)^(-2)` abelianizes to
`lambda_(i+1)^(-1)`, so `c = -1` on one relator and `C_Hig = 1`.  The
hypothesis "no nontrivial finite quotient" for Higman is item 1 of
`higman-group-embeds-in-no-almost-automorphism-group`, applied with `T`
finite and discrete: every relation-satisfying quadruple in a finite group
is trivial.  That item uses the same convention
`g_i g_(i+1) g_i^(-1) = g_(i+1)^2`.

## Step 6: the (CGC) corollary

Given `C_i Z_(i+1) C_i^* = Z_(i+1)^2` and `||Z_(i+1) - C_(i+1)|| <= eta`:

```text
||C_i C_(i+1) C_i^* - C_(i+1)^2||
  <= ||C_i (C_(i+1) - Z_(i+1)) C_i^*|| + ||Z_(i+1)^2 - C_(i+1)^2||
  <= eta + 2 eta.
```

The last step uses `||A^2 - B^2|| <= ||A(A - B)|| + ||(A - B)B||`.  If the
`C_i` generate a finite group and `3 eta < 1/2`, then (FIC) with
`C_Hig = 1` gives `max_i ||C_i - 1|| <= 3 eta`.
