---
rg: 2
id: transported-gap-masa-kills-leavitt-hs-models-proof
kind: route
title: Read the scalar-gap atoms as a masa of the relative commutant and conjugate the Thompson copy into it
target: transported-gap-masa-kills-leavitt-hs-models
requires: [openai-nine-leaf-leavitt-configuration, binary-leavitt-elementary-group-is-simple, leavitt-gl-equals-el-and-perfect-unit-group, steinberg-hs-stability-equals-nonhyperlinearity]
artifacts:
  - c1168433:official/counterexample.tex
---

## Proof of (A)

`A_1 := sigma(t Gamma t^(-1))' cap M = sigma(t) A_0 sigma(t)^*`, so
`B_1 := sigma(t) B sigma(t)^*` is a maximal abelian subalgebra of `A_1`.

* **`sigma(tJt^(-1))` lies in `A_1`,** because `J` commutes with `Gamma`.
* **It also commutes with `B_1`.**  `t J t^(-1) <= Gamma`, so it commutes
  with every element of `A_0`, and `B_1 <= A_0` by hypothesis.

Hence `sigma(tJt^(-1)) <= A_1 cap B_1' = B_1`.  So `sigma(tJt^(-1))` is
abelian, and `sigma(t[J,J]t^(-1)) = 1`.

## Proof of (B)

Fix a free ultrafilter `omega`.  Let `M = prod_omega M_(d_n)` be the tracial
ultraproduct and `sigma = [phi_n]` the induced homomorphism
`G -> U(M)`; write `A_0 = sigma(Gamma)' cap M`.  Put `B_n = span{p_(n,j)}`
and `B = prod_omega B_n`, an abelian subalgebra whose unit is `1` because
`tau(1-p_n) -> 0`.  All estimates below are uniform over coefficients
`|lambda_j| <= 1`.

**Step 1: `B <= A_0`.**  For `b = sum_j lambda_j p_j`,

```text
[phi(s), b] = sum_(k != j) (lambda_j - lambda_k) p_k phi(s) p_j,
||[phi(s), b]||_2^2 <= 4 sum_(k != j) ||p_k phi(s) p_j||_2^2
                    = 2 sum_j ||[phi(s), p_j]||_2^2 -> 0
```

by `(F1)`.

**Step 2: `B` is maximal abelian in `A_0`.**  `A_0 cap B'` is a
`*`-algebra, so it suffices to treat a self-adjoint `a in A_0 cap B'` with
`||a|| <= 1` and self-adjoint representatives `a_n`.  Put
`D_n = sum_j p_j M p_j`.

*`a` is block diagonal.*  If `||a_n - E_(D_n)(a_n)||_2^2 = sum_(k != j)
||p_k a_n p_j||_2^2 >= theta > 0` on an `omega`-large set, average
`||[a_n, sum_j eps_j p_j]||_2^2` over independent random signs `eps_j`.  The
average is `2 sum_(k != j) ||p_k a_n p_j||_2^2 >= 2 theta`, so some bounded
sequence in `B` fails to commute with `a`, a contradiction.  So we may take
`a_n in D_n`.

*`a` is block scalar.*  For `a in D_n` one has
`p_j [phi(s), a] p_j = [p_j phi(s) p_j, a_j]` exactly, where `a_j = p_j a p_j`.
Hence `sum_j ||[p_j phi(s) p_j, a_j]||_2^2 <= ||[phi(s), a]||_2^2 -> 0`.
Apply `(F2)` to the self-adjoint block-diagonal `x = a`:

```text
||a - E_(B_n)(a)||_2^2 = sum_j ||a_j - tau_j(a_j) p_j||_2^2 -> 0.
```

So `a in B`.

**Step 3: `sigma(u) B sigma(u)^* <= B`.**  Put `W = phi_n(u)`,
`y_j = W p_j W^*`, `e_j = ||y_j - p_(sigma(j))||_2^2`, `eps = sum_j e_j -> 0`,
and `t_j = tau(p_j)`.  By the collision count in
`hs-per-atom-compressor-clause-is-vacuous-proof`, the atoms sharing an image
carry total trace at most `8 eps`.  Call the others good; `sigma` is injective
on them with pairwise orthogonal images.

For `b = sum_j lambda_j p_j`, set `b' = sum_(j good) lambda_j p_(sigma(j))`,
which lies in `B_n` with `||b'|| <= 1`.  Then
`W b W^* - b' = sum_(good) lambda_j x_j + sum_(bad) lambda_j y_j`, with
`x_j = y_j - p_(sigma(j))`.

*Bad atoms.*  The `y_j` are orthogonal, so the second sum has squared norm at
most `8 eps`.

*Good atoms.*  The diagonal terms contribute at most `eps`.  For `j != k`,
orthogonality kills `tau(y_k y_j)` and `tau(p_(sigma(k)) p_(sigma(j)))`, so

```text
|sum_(j != k) lambda_j conj(lambda_k) tau(x_k^* x_j)|
  <= 2 sum_k tau(y_k (1 - p_(sigma(k))))
   = sum_k (t_k - t_(sigma(k)) + e_k)
  <= sum_k |t_k - t_(sigma(k))| + eps.
```

Also `|t_k - t_(sigma(k))| <= (e_k (t_k + t_(sigma(k))))^(1/2)`, and
Cauchy--Schwarz over good `k` gives `sum_k |t_k - t_(sigma(k))| <=
(2 eps)^(1/2)`.  Altogether

```text
||W b W^* - b'||_2 <= (2 eps + (2 eps)^(1/2))^(1/2) + (8 eps)^(1/2) -> 0,
```

so `sigma(u) b sigma(u)^* in B`.

**Step 4: conclude.**  By steps 2--3, `B` is a masa of `A_0` with
`sigma(u) B sigma(u)^* <= A_0`.  By `openai-nine-leaf-leavitt-configuration`,
`[Gamma, J] = 1` and `u J u^(-1) = V_(0001) <= Gamma`.  By `(A)`,
`sigma([J,J]) = 1`.  `J ~= V` is nonabelian, so `ker sigma` is a nontrivial
normal subgroup of `G`.  `G = EL_D(R) ~= EL_9(R)` is simple
(`binary-leavitt-elementary-group-is-simple`), so `sigma` is trivial.  This
holds for every free ultrafilter, so `phi_n(g) -> 1` pointwise.

## Proof of (C)

If `hs-expander-block-decomposition` holds, its uniform clauses along any
almost-representation sequence with defects tending to zero give
`(F1)`, `(F2)` and `(MW)` for `u`.  By (B), every such sequence tends to `1`.
A hyperlinear approximation of `G` keeps each `g != 1` at distance tending to
`sqrt 2`, so `G` is not hyperlinear.

The prefix-code self-similarity `R ~= M_9(R) ~= M_4(R)` and
`GL_n(R) = EL_n(R)` (`leavitt-gl-equals-el-and-perfect-unit-group`) identify
`EL_9(R)` with `EL_4(R) = Q`.  So `Q` is nonhyperlinear, which is condition 3
of `steinberg-hs-stability-equals-nonhyperlinearity`, equivalent to
normalized-HS stability of `St_5(L)`.

## The tower in a nontrivial model

If `sigma(J) != 1`, then `sigma` is injective, since `G` is simple.  The
following hold.

* **The inclusions.**  `Gamma_(k+1) <= Gamma_k` gives `A_k <= A_(k+1)`.
  Unitary conjugation gives `A_(k+1) = sigma(u) A_k sigma(u)^*`.
* **Where `V_k` sits.**  `V_k` commutes with `Gamma_k`, so
  `sigma(V_k) <= A_k`.  `V_k <= Gamma_(k-1)` commutes with `A_(k-1)`, so
  `sigma(V_k) <= R_k := A_k cap A_(k-1)'`.
* **Commuting.**  For `j > k`, `R_j <= A_(j-1)'` and `R_k <= A_k <= A_(j-1)`,
  so `R_j` and `R_k` commute.
* **Strictness.**  If `A_(k-1) = A_k`, then `sigma(V_k)` commutes with
  `sigma(Gamma_(k-1))`, which contains it, so `sigma(V_k)` is abelian,
  contradicting injectivity.
* **No masa descends.**  A masa `B_k` of `A_k` inside `A_(k-1)` would contain
  `sigma(V_k)` by the argument of (A), which is again a contradiction.
