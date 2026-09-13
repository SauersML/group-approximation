---
rg: 2
id: cubic-division-congruence-sc-descends-to-thin-subgroups-proof
kind: route
title: Zariski density and strong approximation identify the congruence quotients of a subgroup with those of the lattice; strong convergence restricts
target: cubic-division-congruence-sc-descends-to-thin-subgroups
requires: [cubic-division-lattice-subgroups-are-zariski-dense]
---

1. **Zariski density.**  `H` is nonamenable, so by
   `cubic-division-lattice-subgroups-are-zariski-dense` it is Zariski dense in
   `G = SL_1(D)`.
2. **Onto mod `p`.**  `G` is a simply connected, absolutely almost simple
   `Q`-group (a form of `SL_3`).  `H <= G(Q)` is finitely generated and
   Zariski dense, and it is integral at every prime, since `H <= SL_1(O_D)`.
   Strong approximation for Zariski-dense subgroups (Matthews--Vaserstein--
   Weisfeiler, Proc. LMS 48 (1984); Weisfeiler, Ann. of Math. 120 (1984);
   import, not re-read here, the same import used by the consequence in
   `cubic-division-lattice-subgroups-are-zariski-dense`) makes the closure of
   `H` in `prod_p G(Z_p)` open.  So `H -> G(Z/p) = SL_1(O_D/pO_D) = SL_3(F_p)` is
   onto for every `p` outside a finite set `P_H`, which we take to contain
   `P_D`.
3. **Identification.**  For `p` not in `P_H`, `H` acts on `Q_p = Gamma_D/Gamma_D(p)`
   by left translation through the onto map `H -> Q_p`.  The action is
   transitive with stabiliser `H(p)`, so `Q_p = H/H(p)` as `H`-sets.  The
   constants correspond, so `pi_p|_H = l^2_0(H/H(p))`.
4. **Regular norms restrict.**  `l^2(Gamma_D)` is the orthogonal sum over right
   cosets `Hg` of the `H`-invariant subspaces `l^2(Hg)`, each unitarily
   equivalent to `lambda_H`.  So `||lambda_(Gamma_D)(z)|| = ||lambda_H(z)||` for
   `z in C[H]`.
5. **Conclusion.**  For `z in C[H] <= C[Gamma_D]` and `p` not in `P_H`,
   `||l^2_0(H/H(p))(z)|| = ||pi_p(z)|| -> ||lambda_(Gamma_D)(z)|| = ||lambda_H(z)||`.
   This proves 1 and 2.  For 3, Kesten (Trans. AMS 92 (1959)) gives
   `||lambda_(F_2)(a + a^-1 + b + b^-1)|| = 2 sqrt 3`.  The Cayley graph's adjacency
   operator on mean-zero functions is `pi_p(a + a^-1 + b + b^-1)`.  It is
   self-adjoint, so its norm is the largest nontrivial absolute eigenvalue.
   The contrapositive is 2 read backwards.
