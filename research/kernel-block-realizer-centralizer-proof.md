---
rg: 2
id: kernel-block-realizer-centralizer-proof
kind: route
title: The centralizer factors give a homomorphism of the quotient into a central quotient of a subgroup of the universal sofic group, which acyclicity lifts and trivial sofic morphisms kill
target: kernel-block-realizers-need-no-centralizer-factor
requires:
  - binary-leavitt-unit-group-integrally-acyclic
  - leavitt-unit-group-has-only-trivial-sofic-morphisms
  - hyperbolic-kazhdan-cover-of-leavitt-unit-group
---

The general statement uses only the two hypotheses on `Q`. The prerequisites
supply them, and the extension, for the instance.

1. **Commuting products.** At each stage, a block-preserving permutation that acts
   on every block by an element of `Pi_B` commutes with one that acts on every
   block by an element of `C_B`. Commutation passes to `S_U`, so `[Pi, C] = 1`.
   For `s in S`, `sigma_n(s) = s~` off `o(|X_n|)` points and `s~` lies in
   `prod_B Pi_B`, so `sigma(s) in Pi` and `sigma(N) <= Pi`.
2. **The centralizer homomorphism.** Assume `sigma(G) <= Pi C`. Composing `sigma`
   with the quotient map `Pi C -> Pi C / Pi` gives a homomorphism `theta` that
   kills `N`, so it factors through `theta_bar : Q -> Pi C / Pi`. The inclusion
   `C -> Pi C` induces an isomorphism `C / (C cap Pi) -> Pi C / Pi`; regard
   `theta_bar` as taking values in `C / (C cap Pi)`.
3. **A central extension.** For each `q in Q` choose `c_q in C` representing
   `theta_bar(q)`, and let `E_0 = <c_q : q in Q>`, a countable subgroup of `C`.
   Put `A_0 = E_0 cap Pi`. It is central in `E_0`, because `Pi` commutes with `C`.
   Let

   ```text
   E' = { (q, e) in Q x E_0 :  theta_bar(q) = e (C cap Pi) } .
   ```

   Projection `E' -> Q` is onto, by the `c_q`. Its kernel is `{1} x A_0`, which is
   central. So `E'` is a central extension of `Q` by `A_0`.
4. **It splits.** By universal coefficients,
   `H^2(Q; A_0) = Hom(H_2(Q; Z), A_0) + Ext(H_1(Q; Z), A_0) = 0`. So there is a
   homomorphic section `q -> (q, psi(q))`. Then `psi : Q -> E_0 <= S_U` is a
   homomorphism with `psi(q) (C cap Pi) = theta_bar(q)`.
5. **It is trivial.** Every homomorphism `Q -> S_U` is trivial, so `psi = 1` and
   `theta_bar = 1`. Hence `sigma(G) <= Pi`.
6. **Restriction to a union of blocks.** Let `Y_n` be a union of blocks with
   `|Y_n| >= delta |X_n|` on which every generator of `G` is realized. Realizers
   preserve blocks, so every element of `G` maps `Y_n` into itself off
   `o(|X_n|)` points. The restrictions form a sofic approximation of `G` on `Y_n`:
   fixed points of `sigma_n(g)`, `g != 1`, number `o(|X_n|) = o(|Y_n|)`. Steps
   1-5 apply there.
7. **Instance.** For the Leavitt cover, `Q = R^x` with `R = L_(F_2)(1,2)`.
   `binary-leavitt-unit-group-integrally-acyclic` gives `H_1 = H_2 = 0`, and
   `leavitt-unit-group-has-only-trivial-sofic-morphisms` gives that every
   homomorphism `R^x -> S_U` is trivial. The kernel `N` is Kazhdan by
   `hyperbolic-kazhdan-cover-of-leavitt-unit-group`. ∎
