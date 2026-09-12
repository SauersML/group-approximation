---
rg: 2
id: fp-rf-group-with-unbounded-prime-torsion
kind: claim
title: Some finitely presented residually finite group has elements of prime order for infinitely many primes
distinct_from:
  cycle-transposition-lef-group-has-no-regular-tree-action: that is a finitely generated residually finite group, not known to be finitely presented, with elements of every prime order at least 5; this asks for a finitely presented one.
  kms-arbitrarily-hard-fp-rf-groups: that realizes arbitrarily hard word problems by finitely presented residually finite groups whose torsion involves boundedly many primes; this asks for torsion of infinitely many prime orders.
---

**OPEN.** There is a finitely presented residually finite group `G` such that
infinitely many primes occur as orders of elements of `G`.

**Why it matters.** By `regular-tree-torsion-orders-have-primes-at-most-degree`,
such a `G` embeds in `Aut(T_d)` for no `d`. So it refutes
`every-fp-rf-group-embeds-in-fp-self-similar-group`, through the route
`fp-rf-tree-obstruction-via-unbounded-torsion`.

**Literature status.** Not checked. This session ran no literature search, so
whether such a group is already known is open here.

## Attempts

1. **Linear groups.** *Dies.* Let `G` be a finitely generated subgroup of
   `GL_n(K)`.
   - *Characteristic zero.* `G` has a torsion-free normal subgroup `N` of finite
     index `i` (Selberg). A torsion element meets `N` trivially, so its order
     divides `i`.
   - *Characteristic `p`.* The field of entries contains only a finite field
     `F_q` of algebraic elements. Write a torsion element's order as `p^a m'`
     with `m'` coprime to `p`. Its `p^a`-th power is semisimple of order `m'`,
     with eigenvalues in extensions of `F_q` of degree at most `n`. So `m'`
     divides `lcm_(j <= n) (q^j - 1)`.

   Either way only finitely many primes occur.
2. **Abelian-by-polycyclic groups, including finitely generated metabelian
   groups.** *Dies.* Let `A` be the abelian normal subgroup and `P = G/A`.
   - `A` is a Noetherian `Z[P]`-module (P. Hall), so its torsion submodule is
     finitely generated and has finite exponent `e`.
   - `P` is virtually torsion-free, so its torsion orders divide some `e'`.
   - Every torsion order in `G` divides `e*e'`.
3. **Groups acting properly and cocompactly on CAT(0) spaces, and hyperbolic
   groups.** *Dies.* They have finitely many conjugacy classes of finite
   subgroups. This is standard and was not rechecked against a source here.
4. **Kharlampovich--Myasnikov--Sapir groups.** *Dies for torsion.* By
   arXiv:1204.6506 §1.6 and §4 (Lemma 4.14, Theorem 4.17), `G(M)` is a split extension of an elementary
   abelian group of prime exponent `p` by a metabelian group. By attempt 2, only
   finitely many primes occur.
5. **Finitely presented groups that are not residually finite.** Thompson's `V`
   contains every finite group, but it is simple and infinite. Houghton's `H_3`
   contains the finitary symmetric group. Neither is residually finite.
6. **Finitely generated examples, and why block-diagonal ones resist finite
   presentation.** The group of
   `cycle-transposition-lef-group-has-no-regular-tree-action` has every prime
   order `p >= 5`. Let `G <= prod_m F_m` be finitely generated, with every
   `F_m` finite, and suppose the restricted part `K = G ∩ (+)_m F_m` is
   infinite. Two facts constrain such a `G`.
   - **`G/K` is not finitely presented.** Otherwise, since `G` is finitely
     generated, `K` would be the normal closure in `G` of finitely many elements.
     Each of those has finite support, and conjugation in `prod_m F_m` preserves
     supports, so `K` would be finite.
   - **If `G` is finitely presented, then `G/K` is of type `FP_2` over `Q`.**
     `K` is locally finite, so `Q[K]` is von Neumann regular, every
     `Q[K]`-module is flat, and `Tor_i^(Q[K])(Q, Q) = 0` for `i > 0`. Take a
     projective resolution of `Q` over `Q[G]` that is finitely generated in
     degrees at most `2`, and apply `Q ⊗_(Q[K]) -`. The result is such a
     resolution over `Q[G/K]`.

   For the group above, `G/K` is `FSym(Z) x| Z`: it is the permutation of `Z`
   read off from large coordinates, and step 2 of
   `cycle-transposition-lef-group-proof` shows that this is a well-defined
   homomorphism with kernel `K`. That quotient is Houghton's `H_2`. It is not
   finitely presented, as the first fact confirms. Whether `H_2` is `FP_2` over
   `Q` was not checked here, so finite presentation of the group itself is not
   excluded.

   A finitely presented residually finite overgroup would suffice. That is the
   route `unbounded-prime-torsion-via-rf-higman-embedding`, whose open clause
   is `rf-higman-embedding-for-decidable-groups`.
