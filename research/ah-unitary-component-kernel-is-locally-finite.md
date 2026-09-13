---
rg: 2
id: ah-unitary-component-kernel-is-locally-finite
kind: claim
title: In a unital AH limit the kernel of U/U0 -> K1 is locally finite, so finitely generated subgroups of U/U0 are center-by-finite
distinct_from:
  block-component-group-class-at-most-excess-plus-two: That bounds the nilpotency class of a block group by the excess; this shows the K1-kernel of a block group is finite, which bounds orders, not class.
  simple-ah-algebra-with-class-three-component-group: That builds one order-two triple commutator; this constrains every commutator in every unital AH limit.
---

Let X be a connected finite CW complex of dimension d, E -> X a Hermitian
bundle of rank r, Pi(E) = pi_0 U(Gamma(End E)), and
kappa_E: Pi(E) -> K^1(X) the K_1 map. Let A = lim (A_i, phi_i) be a unital
inductive limit with injective unital connecting maps, each A_i a finite
direct sum of such algebras Gamma(End E), and kappa: U(A)/U_0(A) -> K_1(A).

(a) N(E) = ker kappa_E is a finite nilpotent group. Its order divides
    prod_{2r <= k <= d} |pi_k U(r)|^{c_k}, where c_k is the number of k-cells.
(b) ker kappa is locally finite and locally nilpotent. So it is the direct
    sum of its Sylow p-subgroups, and it contains the commutator subgroup of
    U(A)/U_0(A). Every nontrivial commutator has finite order.
(c) Every finitely generated subgroup H of U(A)/U_0(A) has a finite
    commutator subgroup and a center of finite index. In particular no
    finitely generated subgroup is a torsion-free nonabelian group, such as
    the integer Heisenberg group.
(d) Every x in ker kappa dies after finite matrix amplification: for some m,
    diag(x, 1_m) lies in U_0(M_{1+m}(A)).

So a non-nilpotent AH component group can only arise from finite p-group
pieces of unbounded class, carried by blocks of unbounded excess
(block-component-group-class-at-most-excess-plus-two). The order-two witness
of simple-ah-algebra-with-class-three-component-group, which dies in M_2, is
the first instance of (b) and (d).

Proof: route ah-unitary-component-kernel-locally-finite-proof. Not
independently reviewed.
