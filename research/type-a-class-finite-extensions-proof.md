---
rg: 2
id: type-a-class-finite-extensions-proof
kind: route
title: Embed products in products of actors and finite extensions in finite wreaths, then apply Corollary B
target: boone-higman-type-a-class-closed-under-finite-extensions
requires:
  - type-a-actions-closed-under-products-and-finite-wreaths
  - type-a-action-gives-boone-higman-for-subgroups
---

1. **Subgroups.** A subgroup of a subgroup of an actor is a subgroup of that
   actor.

2. **Products.** If `G_1 <= Gamma_1` and `G_2 <= Gamma_2`, with each `Gamma_i`
   admitting a type (A) action, then `G_1 x G_2 <= Gamma_1 x Gamma_2`. The
   latter admits a type (A) action by part (a) of
   `type-a-actions-closed-under-products-and-finite-wreaths`. Induct on the
   number of factors.

3. **Finite-index overgroups.** Let `H <= G` have index `k`, and let
   `H <= Gamma` with `Gamma` admitting a type (A) action on a nonempty set.
   - By the Kaloujnine--Krasner embedding theorem (classical: induction from `H`
     to `G` as monomial matrices over `H`), `G` embeds in the permutational
     wreath product `H wr S_k = H^k x| S_k`.
   - This wreath product is a subgroup of `Gamma wr S_k`, which admits a type (A)
     action by part (b) of the same claim.
   - Hence `G` is in `B_A`.

4. **Envelopes and word problem.** Zaremsky's Corollary B, imported as
   `type-a-action-gives-boone-higman-for-subgroups`, gives both conclusions for
   every subgroup of a group admitting a type (A) action.

The consequence stated in the claim follows by applying 2 and then 3. ∎

The only external input beyond the two required claims is the
Kaloujnine--Krasner theorem, a standard textbook result not re-read for this
node.
