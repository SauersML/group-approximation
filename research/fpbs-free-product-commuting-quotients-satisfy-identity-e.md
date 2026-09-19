---
rg: 2
id: fpbs-free-product-commuting-quotients-satisfy-identity-e
kind: claim
title: On a free product with union generators, every normal subgroup containing the commutator of the factors satisfies p_c(N;G) = p^Q_(2->2)(N;G), with an explicit renewal formula and a Kesten gap exactly when the quotient is nonamenable
distinct_from:
  fpbs-relative-threshold-is-quotient-l2-threshold: that asserts the identity for every normal subgroup of every Cayley graph and is OPEN; this proves it on one class, where the fibre kernel is a resolvent of a single symmetric renewal kernel on the quotient
  fpbs-tree-product-fibre-operator-is-half-tilted-susceptibility: that settles type (i) on tree products Lambda x H_grp along H_grp, where E itself stays open; this proves E itself, on free products, including arbitrary nonamenable quotients Q = H whose Cayley graphs are not trees
  fpbs-tree-normal-relative-threshold-is-inverse-cogrowth: that is the free-group tree, whose blocks are single edges and whose normal subgroups are arbitrary; this allows arbitrary factor blocks but only normal subgroups whose quotient makes the factor images commute
  fpbs-free-product-cayley-graphs-have-critical-l2-gap: that is p_c < p_(2->2) on the same graphs; this is the relative threshold of normal subgroups there, and the critical fibre l2 condition along them
---

**ESTABLISHED.** Proof in
`fpbs-free-product-commuting-quotients-identity-e-proof`.

**Setting.**

- `A` and `H` are nontrivial finitely generated groups, not both of order 2.
- `S_A` and `S_H` are finite symmetric generating sets without `e`. Put
  `Gamma = A * H`, `S = S_A ⊔ S_H` and `G = Cay(Gamma,S)`.
- `pi: Gamma -> Q` is a surjective homomorphism such that `pi(A)` and `pi(H)`
  commute. Equivalently, `N = ker pi` contains `[A,H]`. Such an `N` is
  infinite.
- `tau^A_p` and `tau^H_p` are the two-point functions of the factor Cayley
  graphs. Put
  - `alpha_p = pi_*(tau^A_p - delta_e)`;
  - `beta_p = pi_*(tau^H_p - delta_e)`;
  - `f_p = alpha_p * beta_p`, a symmetric function on `Q` with values in
    `[0,infinity]`.
- `||.||_Q` is the positive-kernel norm of `fpbs-quotient-l2-threshold-sandwich`.

**Theorem.**

1. **(Renewal formula.)** As functions on `Q` with values in `[0,infinity]`,

   ```text
   sigma^N_p = (delta_e + alpha_p) * (delta_e + beta_p) * sum_(k>=0) f_p^(*k).
   ```

2. **(Claim E holds.)** `p_c(N;G) = p^Q_(2->2)(N;G) = sup{ p : ||f_p||_Q < 1 }`.
3. **(Kesten gap, type (i).)** If `Q` is nonamenable, then
   `||sigma^N_(p_c)||_Q < infinity`. So `p_c(G) < p_c(N;G)` and the pair is of
   type (i) in C1 of `fpbs-relative-threshold-is-quotient-l2-threshold`. If
   `Q` is amenable, then `p_c(N;G) = p_c(G)`.

**Special cases.**

- **`N = <<A>>`, `Q = H`.** Here `alpha_p = (chi^A_p - 1) delta_e`. So
  `p_c(N;G)` is the root of `(chi^A_p - 1)(||T^H_p|| - 1) = 1`.
- **`N = [A,H]`, `Q = A x H`.** Here `p_c(N;G)` is the root of
  `(||T^A_p|| - 1)(||T^H_p|| - 1) = 1`.
- **Compare `p_c(G)`.** It is the root of `(chi^A_p - 1)(chi^H_p - 1) = 1`
  (Kozáková). This is the same formula for the trivial quotient.

Here the root means the supremum of the `p` at which the left side is below 1.
The left side is strictly increasing in `p` wherever it is finite.

**What it changes for the belief.**

- Claim E now holds on a class that has non-tree nonamenable quotients: any
  `H`, including Kazhdan groups, with `Q = H`. It also holds with generating
  sets that are not product sets.
- So the w12 "next test" for a type-(ii) pair is answered negatively on free
  products.
- The invariant that forces E is the **renewal structure**: `sigma^N_p` is a
  resolvent `g * sum f^(*k)` of one symmetric kernel `f`, with `g >= delta_e`.
  - Then `sigma(e) < infinity` forces `sum_k f^(*k)(e) < infinity`, which
    forces `||f||_Q <= 1` by the diagonal formula.
  - Strict monotonicity `f_p <= c f_(p')`, with `c < 1`, then puts every
    smaller `p` in the l2 regime.
- A type-(ii) pair therefore needs a fibre kernel that is not dominated by a
  resolvent whose diagonal is controlled by `sigma(e)`. This rules out
  cut-point renewals over the quotient, such as free-product blocks and
  tree-like pieces glued at single vertices.
