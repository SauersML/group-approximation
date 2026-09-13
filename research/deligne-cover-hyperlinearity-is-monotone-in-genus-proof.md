---
rg: 2
id: deligne-cover-hyperlinearity-is-monotone-in-genus-proof
kind: route
title: The block embedding restricts to U(g) -> U(g+1), u -> diag(u,1), which is an isomorphism on pi_1; lift it to the universal covers
target: deligne-cover-hyperlinearity-is-monotone-in-genus
requires: []
---

**The block embedding.** Use the form `J_g = [[0, I_g], [-I_g, 0]]`. For
`A = [[a, b], [c, d]]` with `g x g` blocks, put `iota(A) = [[a', b'], [c', d']]`, where
`a' = diag(a, 1)`, `b' = diag(b, 0)`, `c' = diag(c, 0)` and `d' = diag(d, 1)`. Then
`iota(A)^T J_(g+1) iota(A) = J_(g+1)`. `iota` is an injective continuous homomorphism, and
`iota(Sp_(2g)(Z)) <= Sp_(2g+2)(Z)`.

**Fundamental groups.**
- `K_g = Sp_(2g)(R) cap O(2g)` consists of the matrices `[[a, b], [-b, a]]`. It is identified with
  `U(g)` by `a + ib`.
- The inclusion `K_g -> G_g` is a homotopy equivalence (polar decomposition), so
  `pi_1(G_g) = pi_1(U(g)) = Z`, detected by `det : U(g) -> S^1`.
- `iota` maps `K_g` into `K_(g+1)` as `u -> diag(u, 1)`, and `det diag(u, 1) = det u`.
- So `iota_* : pi_1(G_g) -> pi_1(G_(g+1))` is an isomorphism.

**Item 1.**
- `G~_g` is simply connected, so `iota o p_g` lifts uniquely to a continuous map
  `iota~ : G~_g -> G~_(g+1)` with `iota~(e) = e`. Lifts of homomorphisms between connected Lie
  groups to universal covers are homomorphisms, so `iota~` is one.
- On `ker p_g = pi_1(G_g)` the lift acts as `iota_*`, an isomorphism onto `ker p_(g+1)`. Choose
  generators with `iota~(z_g) = z_(g+1)`.
- **Injective.** If `iota~(x) = e`, then `iota(p_g(x)) = e`, so `p_g(x) = e`. Hence `x` lies in
  `ker p_g`, where `iota~` is injective, so `x = e`.
- **Preimages.** `iota~(Gamma~_g)` maps onto `iota(Sp_(2g)(Z))` and contains
  `ker p_(g+1) = iota~(ker p_g)`. So it equals `p_(g+1)^(-1)(iota(Sp_(2g)(Z)))`.
- **Quotients.** Suppose `iota~(x)` lies in `<z_(g+1)^n>`, say `iota~(x) = z_(g+1)^(nj)`. This equals
  `iota~(z_g^(nj))`, so injectivity gives `x = z_g^(nj)`. Hence `iota~` induces an injection
  `E_n^(g) -> E_n^(g+1)`, and the covering generator goes to the covering generator. For
  `n = infinity` there is nothing to quotient.

**Item 2.** Hyperlinearity, soficity, the MF property and linear soficity all pass to subgroups.

**Item 3.**
- Let `phi_k` be an asymptotic homomorphism of `E_n^(g+1)` in the given metric class. The
  definitions are pointwise.
- Then `phi_k o iota~` is an asymptotic homomorphism of `E_n^(g)`. By hypothesis it sends `z_g^k` to
  `1` asymptotically.
- `iota~(z_g^k) = z_(g+1)^k`, which proves the claim.
- For the presentation-based forms such as `(DCM1)`: every relator of `E_n^(g)`, written in
  generators of `E_n^(g+1)`, is a relation of `E_n^(g+1)`. So its defect under a vanishing-defect
  model of `E_n^(g+1)` tends to zero.

**Item 4.**
- By item 1, the restriction of the universal-cover extension of `Sp_(2g+2)(Z)` to
  `iota(Sp_(2g)(Z))` is the universal-cover extension of `Sp_(2g)(Z)`. So `b_(g+1) o (iota x iota)`
  is cohomologous to `b_g`.
- Cohomologous cocycles give isomorphic twisted group von Neumann algebras. The unitaries
  `u_(iota(x))`, `x in Sp_(2g)(Z)`, generate a copy of `L_(exp(2 pi i t b_g))(Sp_(2g)(Z))` inside
  `L_(exp(2 pi i t b_(g+1)))(Sp_(2g+2)(Z))`. The inclusion is trace preserving because
  `tau(u_(iota(x))) = delta_(x,e)`.
- A von Neumann subalgebra of a Connes-embeddable finite algebra is Connes embeddable.

**Item 5.**
- A countable group is hyperlinear iff each of its finitely generated subgroups is.
- Every finitely generated subgroup of the direct limit `E_3^(infinity)` lies in some `E_3^(g)`.
- By item 2, non-hyperlinearity at one genus persists at all higher genera.
