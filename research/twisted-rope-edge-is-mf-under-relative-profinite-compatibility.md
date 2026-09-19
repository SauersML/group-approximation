---
rg: 2
id: twisted-rope-edge-is-mf-under-relative-profinite-compatibility
kind: claim
title: The twisted rope edge is MF when the base has finite quotients refining the twist
distinct_from:
  profinite-synchronized-hnn-is-regular-mf: that requires the whole base to be residually finite (its hypothesis PSH1) and goes through Ueda's corner and Shulman's corona criterion; this needs only MF of the first factor plus closedness of S and refinement of the twist, which is what the Higman rope can offer since its witness group is not residually finite, and it proves group-level MF directly from finite HNN quotients and a retraction.
  asymmetric-hnn-embeds-in-central-hnn-of-inner-envelope: that is the structural embedding into a central HNN extension; this is a sufficient condition, with proof, for MF of the specific product-twist edge, using finite HNN quotients and a retraction.
  mf-safe-asymmetric-hnn-replacement: that records the edge as the open obstruction; this is a theorem reducing it to a purely profinite condition on the benign witness.
  regular-mf-central-hnn-closure: that concerns stable letters centralizing a subgroup; here the stable letter shears one coordinate by a homomorphism.
---

ESTABLISHED.  Let `Gamma` be a countable MF group, `S <= Gamma`, `Q` a
countable residually finite group, `tau : S -> Q` a homomorphism, and

```text
R = < Gamma x Q, u | u (s,1) u^-1 = (s, tau(s)),  s in S >.         (TE1)
```

Suppose `Gamma` has a decreasing sequence of finite-index normal subgroups
`Gamma_k` such that

```text
(i)   intersection_k  S Gamma_k = S,
(ii)  for every finite-index normal Q' <= Q there is k with
      tau(S cap Gamma_k) <= Q'.                                       (TE2)
```

Then `R` is operator-MF (it embeds in the unitary group of `prod M_n /
(+) M_n`).

Nothing is assumed about `Gamma` beyond MF and the two profinite conditions;
in particular `Gamma` need not be residually finite, which is the situation
of the Higman rope.  This is the point of the theorem relative to
[[profinite-synchronized-hnn-is-regular-mf]], whose hypothesis `(PSH1)`
asks every nonidentity element of `Gamma x Q` to survive in finite
quotients: the witness `Gamma = < K, v | [v,L] = 1 >` centralizes a
distorted subgroup and has a nontrivial profinite kernel, so `(PSH1)` is
unavailable there, while `(TE2)` only constrains the finite quotients of
`Gamma` on `S`.

## Proof

Write `A = Gamma x Q`, `C_1 = S x 1`, `C_2 = {(s,tau(s))}`, `phi(s,1) =
(s,tau(s))`.  Fix a decreasing filtration `Q_k` of `Q` by finite-index normal
subgroups with trivial intersection and, passing to a subsequence of the
`Gamma_k`, assume `tau(S cap Gamma_k) <= Q_k` for all `k`.  Put `A_k =
Gamma_k x Q_k`, a finite-index normal subgroup of `A`, and `M_k = S cap
Gamma_k`.

*Step 1: finite HNN quotients.*  `C_1 cap A_k = M_k x 1` and `phi(M_k x 1) =
{(m,tau(m)) : m in M_k} <= A_k` because `tau(M_k) <= Q_k`; conversely an
element `(s,tau(s))` of `C_2 cap A_k` has `s in M_k`.  So `phi(C_1 cap A_k) =
C_2 cap A_k`, `phi` descends to an isomorphism `C_1A_k/A_k -> C_2A_k/A_k`,
and

```text
D_k = < A/A_k, u | u cbar u^-1 = phibar(cbar) >
```

is an HNN extension of a finite group, with a homomorphism `rho_k : R ->
D_k` extending `A -> A/A_k`.  `D_k` acts on its Bass--Serre tree with finite
stabilizers, so it is virtually free and residually finite.

*Step 2: reduced words stay reduced.*  Let `a = (g,q) in A`.  If `a notin
C_1`, then either `q != 1`, and `a notin C_1 A_k` as soon as `q notin Q_k`,
or `q = 1` and `g notin S`, and `a notin C_1 A_k` as soon as `g notin S
Gamma_k`, which happens for large `k` by `(i)`.  If `a notin C_2`: if `g
notin S` the same argument applies; if `g in S` then `q != tau(g)`, and `a in
C_2 A_k` would give `s in S` with `s^-1 g in M_k` and `q in tau(s) Q_k =
tau(g) Q_k`, impossible for large `k` since `tau(g)^-1 q != 1`.  Hence for
every Britton-reduced word `r = a_0 u^(e_1) a_1 ... u^(e_m) a_m` in `R`, the
image `rho_k(r)` is Britton-reduced in `D_k` for all large `k`, and therefore
nontrivial.

*Step 3: the retraction.*  The assignment `(g,q) -> g`, `u -> 1` respects
`(TE1)` and defines a homomorphism `p : R -> Gamma` with `p|_Gamma = id`.

*Step 4: the embedding.*  Let `Phi_Gamma : Gamma -> U(prod M_(d_n) / (+)
M_(d_n))` be injective, represented by unitaries `U_n(g)`.  Enumerate `R =
{r_1, r_2, ...}`.  For each `k` choose a finite quotient `pi_k : D_k -> G_k`
that is injective on the images `rho_k(r_j)`, `j <= k`, that are nontrivial,
and let `lambda_k` be the left regular representation of `G_k`.  Define

```text
W_k(r) = (U_k(p(r)) (+) 1) (x) lambda_k(pi_k rho_k(r)).             (TE3)
```

The first factor is asymptotically multiplicative because `Phi_Gamma` and
`p` are homomorphisms, the second is exactly multiplicative, so `r ->
(W_k(r))_k` is a homomorphism `Phi : R -> U(prod M_(N_k) / (+) M_(N_k))`.

*Step 5: injectivity.*  Let `r != 1`.  If `p(r) != 1`, then `||U_k(p(r)) -
1||` does not tend to `0`.  A tensor product `X (x) Y` of unitaries within
`eps` of `1` forces every eigenvalue of `X` into an arc of width `o(1)` as
`eps -> 0`; since `X = U_k(p(r)) (+) 1` has eigenvalue `1`, `||W_k(r) - 1||
-> 0` would force `||U_k(p(r)) - 1|| -> 0`, a contradiction.  If `p(r) = 1`
and `r in A`, then `r = (1,q)` with `q != 1`, so `rho_k(r) != 1` once `q
notin Q_k`.  If `p(r) = 1` and `r notin A`, Step 2 gives `rho_k(r) != 1` for
large `k`.  In both cases `pi_k rho_k(r) != 1` for large `k >= j` (where `r
= r_j`), so `lambda_k(pi_k rho_k(r))` is a fixed-point-free permutation
matrix, which has an eigenvalue `omega` with `|omega - 1| >= sqrt 3`; since
`X` has eigenvalue `1`, `X (x) lambda_k` has eigenvalue `omega` and
`||W_k(r) - 1|| >= sqrt 3` for all large `k`.  So `Phi(r) != 1`.

Hence `Phi` is injective and `R` is MF.

## What it buys for the rope

For the Higman rope with `S = F *_N F` inside `Gamma = < K, v | [v,L] = 1 >`
and `tau` the fold, condition `(ii)` for the finite-index subgroup `F' >= N`
of `F` follows from one finite quotient of `Gamma` through which the fold
factors modulo `F'`; a sufficient shape is a homomorphism `K -> (F/F') wr
C_2` with `f -> (fbar, 1)` on `F` and `L` inside the centralizer of the swap,
with `v` sent to the swap.  The open question is recorded as
[[benign-witness-finite-quotients-refine-the-fold]].
