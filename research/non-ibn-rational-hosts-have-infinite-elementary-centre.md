---
rg: 2
id: non-ibn-rational-hosts-have-infinite-elementary-centre
kind: claim
title: Rings with L isomorphic to L^(1+d) and rational centre have elementary groups with infinitely generated centre, so no such ring is a projective-simple host
distinct_from:
  subshift-el-group-centre-detects-rational-eigenvalues: that computes Z(EL_n) over finite-field crossed products, where the scalar group is finite and the answer depends on dynamical eigenvalues; this shows that over any ring with L = L^(1+d) and Q in the centre, all d-th powers of rational scalars are elementary, so the centre is never finitely generated.
  char-zero-algebra-unit-hosts-exclude-unipotents: that obstructs simple unit-group quotients over bounded-divisibility rings via unipotents; this obstructs finite generation of Z(EL_n) over non-IBN Q-algebras, where bounded divisibility fails, and needs no unipotent.
  ring-simple-envelope-characteristic-obstruction: that obstructs simple envelopes by mixed characteristic; this obstructs characteristic-zero non-IBN hosts by the infinite rank of Q^x.
  positive-char-surface-linear-groups-satisfy-boone-higman: that uses Leavitt-tensor hosts over F_p, whose scalar group F_p^x is finite; this shows the same non-IBN host type fails clause 2 of the projective host statement in characteristic zero.
---

**ESTABLISHED.** Let `L` be a unital ring. Suppose `L_L ≅ L_L^{1+d}` as right modules for some `d >= 1`; equivalently, some Leavitt ring `L_Z(1, 1+d)` maps unitally to `L`. Let `U = L^×`.

1. Every central unit `μ` satisfies `μ^d ∈ [U, U]`. For `d = 1`, every central unit is a product of commutators of units.
2. For `n >= 3` and every central unit `μ`, `μ^d I_n ∈ E_n(L)`, and it is central in `EL_n(L)`.
3. If moreover `Q ⊆ Z(L)`, then `Z(EL_n(L))` contains `{λ^d I_n : λ ∈ Q^×}`, which is free abelian of infinite rank modulo torsion. So `Z(EL_n(L))` is not finitely generated for any `n >= 3`.

**Consequence for the projective host hole.**
- Clause 2 of [[decidable-group-ring-has-fp-projective-simple-host]] fails for every such `L` containing `Z[H]` with `Q ⊆ Z(L)`.
- A candidate satisfying clause 3 is a simple ring containing `Z`, so `Q ⊆ Z(L)` automatically.
- So every characteristic-zero non-IBN host of type `1 ≅ 1+d` is excluded. Examples include `B ⊗ L_K(1, 1+d)` over any characteristic-zero field `K`, and any ring receiving a unital map from a Leavitt algebra.

**The invariant and where it dies.**
- The invariant is the rational scalar group `Q^× I_n ⊆ Z(GL_n(L))`.
- In a non-IBN ring, `[1] = (1+d)[1]` forces `d`-th powers of scalars into the commutator subgroup.
- Every member of the class dies at clause 2, finite generation of the centre.
- In characteristic `p` the same mechanism only produces the finite group `F_p^×`, which is why the char-p Leavitt-tensor technology does not transplant.

**Surviving host types.** Surviving hosts must have `Q^× ∩ [U,U]` finitely generated. Two cases remain:
- stably finite (IBN) hosts;
- purely infinite hosts where `[1]` has infinite order in `K_0` and `K_1` detects `Q^×`.
