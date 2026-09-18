---
rg: 2
id: support-covariant-models-carry-fixed-point-trace-proof
kind: route
title: Split the moved set into pieces disjoint from their images, kill the trace on each piece by covariance, and read off the fixed-set contribution from the support axiom
target: support-covariant-models-carry-fixed-point-trace
requires:
  - dense-full-group-subgroups-generate-relation-factor
---

Write `e_A = e(1_A)`.

**Step 1 (moved set splits into displaced pieces).** Fix `g` and let `F = Fix g` and `D = X \ F`. Let `(U_k)` be a
countable family of Borel sets that separates points and is closed under complements. For `x in D` we have
`g x != x`, so some `U_k` contains `x` and not `g x`. Put `A_k = {x in D : x in U_k, g x notin U_k}`. Then
`D = ∪_k A_k`, and `g A_k ∩ A_k = ∅`: if `y = g x` with `x in A_k`, then `y notin U_k`, so `y notin A_k`. Put
`D_k = A_k \ ∪_(j<k) A_j`. The `D_k` are disjoint, cover `D`, and satisfy `g D_k ∩ D_k = ∅`.

**Step 2 (displaced pieces carry no trace).** Replacing `g` by `g^-1` in the covariance relation gives
`pi(g)^* e(f) pi(g) = e(f o g)`. For `A` with `g A ∩ A = ∅`, the trace property gives

```text
tau(pi(g) e_A) = tau(pi(g) e_A e_A) = tau(e_A pi(g) e_A) = tau(pi(g) [pi(g)^* e_A pi(g)] e_A)
               = tau(pi(g) e(1_(g^-1 A)) e(1_A)) = tau(pi(g) e(1_(g^-1 A ∩ A))) = 0,
```

because `g^-1 A ∩ A = g^-1 (A ∩ g A) = ∅`.

**Step 3 (sum).** In `L^infinity(X)`, `1 = 1_F + sum_k 1_(D_k)` with weak-* convergence of the partial sums. `e` is
normal, so the partial sums of `e_F + sum_k e_(D_k)` converge strongly to `1`. `x -> tau(pi(g) x)` is normal, so

```text
tau(pi(g)) = tau(pi(g) e_F) + sum_k tau(pi(g) e_(D_k)) = tau(e_F) + 0 = mu(Fix g),
```

by the support axiom `pi(g) e_F = e_F` and trace preservation of `e`.

**Step 4 (GNS).** `N = W*(pi(Gamma)) <= M` with `tau|N` is a faithful normal tracial state, and the trace vector is
cyclic for `N` in `L^2(N, tau)`. The map `g -> pi(g)` is a unitary representation whose coefficient at the trace
vector is `chi(g) = mu(Fix g)`. By uniqueness of the GNS construction, `(N, tau|N)` is trace-preservingly
isomorphic to the GNS von Neumann algebra of `chi`, with `pi(g)` corresponding to the GNS unitary of `g`. This is
item 1.

**Step 5 (dense subgroups).** Under the hypotheses of item 2, `dense-full-group-subgroups-generate-relation-factor`
gives that the GNS algebra of `chi_R|Gamma` is `(L(R), tau_R)`, with `g -> u_g`. By Step 4, `N ≅ L(R)`
trace-preservingly. If `M` embeds trace-preservingly in `R^U`, so does `N`, and hence `L(R)`. So a non-CE `L(R)`
admits no support-covariant model in a CE algebra.

**Remarks checked in the claim.**
- **Canonical model.** In `L(R)` on `L^2(R)`, `(u_g 1_F xi)(x, y) = 1_F(g^-1 x) xi(g^-1 x, y) = 1_F(x) xi(x, y)`, since
  `g^-1 x = x` on `F` and `g^-1` preserves `X \ F`. So the canonical model is support-covariant.
- **Crossed product.** In `L^infinity(X) ⋊ Gamma`, `u_g e_F` has Fourier coefficient `1_F` at `g`, while `e_F` is
  supported at `e`. So the support axiom fails whenever `g != e` and `mu(Fix g) > 0`.
