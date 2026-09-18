---
rg: 2
id: equivariant-partition-stability-reduction-proof
kind: route
title: Square the right-vertex plurality, realise the second neighbour as a label relabelling of a resampled first neighbour, average the relabelling into an equivariant partition, and apply Cauchy--Schwarz through the idempotent conditional expectations
target: rotated-frame-value-reduces-to-partition-stability
requires: []
artifacts:
  - experiments/pair-resampling-hypercontractivity-2026-09-17/linear_partition_stability.py
---

Notation is as in the target claim. `p_P(a)` is the `P`-partner of `a`, so
`P^(-1)(P(a)) = {a, p_P(a)}`. Row permutations act by
`(sigma X)_a = x_(sigma^(-1)(a))`.

**Step 1 (item 1).**

* **Fractional partition.** `rho_(A,c) >= 0`, and
  `sum_c rho_(A,c)(X) = E_sigma sum_c 1{A(sigma X) = sigma(c)} = 1`.
* **Equivariance.** Put `sigma' = sigma tau`, which is uniform. Then
  `rho_(A,c)(tau X) = E_sigma 1{A(sigma tau X) = sigma(c)} = E_(sigma') 1{A(sigma' X) = sigma' tau^(-1)(c)} = rho_(A, tau^(-1)(c))(X)`.
* **Balance.** Left multiplication by a permutation matrix preserves `mu` and
  fixes `s`. So the conditional law of `X` given `s` is invariant under row
  permutations, and `E[rho_(A,c) | s] = E[rho_(A, tau^(-1)(c)) | s]` for every
  `tau`. The `2n` conditional expectations are equal and sum to 1.

**Step 2 (squaring).** Fix `(A, B)`. Let `q_b(Y) = Pr[P(A(X)) = b | Y]`. Then

`Pr[P(A(X)) = B(Y)] = E_Y q_(B(Y))(Y) <= E_Y (sum_b q_b^2)^(1/2) <= (E_Y sum_b q_b^2)^(1/2) = LL^(1/2)`,

where `LL = Pr[P(A(X)) = P'(A(X'))]`, and `(X,P)`, `(X',P')` are conditionally
independent given `Y`, each with the edge law conditioned on `Y`.

**Step 3 (realising the second neighbour).** Let `X''` be drawn from the law of
`X` given `(P, Y)`, independently of `X` given `(P,Y)`. So `X''` is `X` with
its difference vectors resampled, and `E[f(X'') | X, P] = (T_P f)(X)`. Let
`sigma` be uniform in `S_2n`, independent of everything, and set
`X' = sigma X''` and `P' = P o sigma^(-1)`.

* **Same right vertex.** `Pi_(P') X'` has `b`-th entry
  `sum_(a : P(sigma^(-1) a) = b) x''_(sigma^(-1)(a)) = sum_(c : P(c) = b) x''_c = y_b`.
  So `Pi_(P') X' = Y`.
* **Correct law and independence.** `P'` is uniform on labelled 2-to-1 maps
  whatever `P` is, so `P'` is independent of `(X, P, Y)`. By richness `P` is
  uniform and independent of `Y`, so `P'` has the right conditional law.
  Given `(X, P, Y, P')`, the law of `X' = sigma X''` is the image under
  `sigma` of `law(X | P, Y)`. Row permutation preserves `mu` and maps the
  fibre `{Pi_P X = Y}` onto `{Pi_(P o sigma^(-1)) X = Y}`, so this image is
  `law(X | P', Y)`. Hence `(X', P')` has the conditional edge law given `Y` and
  is independent of `(X, P)` given `Y`.

Therefore

`LL = Pr[P(A(X)) = P(sigma^(-1)(A(sigma X'')))] = E_sigma Pr[P(A(X)) = P(A_sigma(X''))]`,

with `A_sigma(W) = sigma^(-1)(A(sigma W))`.

**Step 4 (averaging the relabelling).** Condition on `(X, P, X'')`. The event
`P(A(X)) = P(A_sigma(X''))` says `A_sigma(X'') in {A(X), p_P(A(X))}`. Averaging
over `sigma` and using `Pr_sigma[A_sigma(W) = c] = rho_(A,c)(W)`:

`LL = E_(X,P,X'') [rho_(A, A(X))(X'') + rho_(A, p_P(A(X)))(X'')]`.

Write `S_a(X) = 1{A(X) = a}` and take the expectation over `X''` given `(X, P)`:

`LL = E_P sum_a ( <S_a, T_P rho_(A,a)> + <S_a, T_P rho_(A, p_P(a))> )`,

with inner products in `L^2(mu)`. Here `X` is independent of `P`, and `p_P` is
fixed once `P` is.

**Step 5 (Cauchy--Schwarz).** `T_P` is a self-adjoint idempotent, so
`<S_a, T_P g> = <T_P S_a, T_P g>`. By Cauchy--Schwarz over `(a, X)`:

`sum_a <T_P S_a, T_P rho_(A,a)> <= (sum_a ||T_P S_a||^2)^(1/2) (sum_a ||T_P rho_(A,a)||^2)^(1/2)`.

The partner term gives the same bound, since `p_P` is a bijection of `[2n]`.
Write `Stab_P(g) = sum_a ||T_P g_a||^2 = sum_a <g_a, T_P g_a>`. Then

`LL <= 2 E_P (Stab_P(S) Stab_P(rho_A))^(1/2) <= 2 (E_P Stab_P(S))^(1/2) (E_P Stab_P(rho_A))^(1/2) = 2 Stab_T(S)^(1/2) Stab_T(rho_A)^(1/2)`.

Finally `Stab_T(S) <= sum_a ||S_a||^2 = 1`, since `T_P` is a contraction. So
`LL <= 2 Stab_T(rho_A)^(1/2)`, and with Step 2,
`Pr[P(A(X)) = B(Y)]^4 <= LL^2 <= 4 Stab_T(rho_A)`. This is item 2.

**Step 6 (item 3).** `s = sum_b y_b` is `sigma(Pi_P X)`-measurable for every
`P`. By the tower property,

`<rho_a, T rho_a> = E_P ||T_P rho_a||^2 >= E_P ||E[T_P rho_a | s]||^2 = ||E[rho_a | s]||^2`.

With balance, summing over `a` gives `Stab_T(rho) >= 2n (1/(2n))^2 = 1/(2n)`. If
`A = F(s)`, then `A(sigma X) = F(s(X))` for all `sigma`. So
`rho_(A,c) = Pr_sigma[sigma(c) = F(s)] = 1/(2n)`, which is `T`-invariant, and
`Stab_T = 1/(2n)`.

For `d = 2n`, `Y` determines `span(y)^perp = span(z)`. Resampling the `z_b` as
a Haar `n`-frame of that span, with squared norms 2, is left multiplication of
`X` by `K_P(M) = H_P^T diag(I, M) H_P`. Here `H_P` is the orthogonal change of
basis to the normalised `e_a + e_a'` and `e_a - e_a'`, and `M` is Haar in
`O(n)`.

**Step 7 (item 4).** Item 2 gives `val(U_(n,d_n))^4 <= 4 sup_rho Stab_T(rho)`.
Suppose the premise makes the sup tend to 0. Then `val -> 0`. The perfect SDP
solution is Step 0 of `walsh-frame-rich-2to1-value-proof`, read as an identity
`z(v,b) = z(u,a) + z(u,a')`. Richness is the paragraph in the target. No
finite-instance claim is made.
