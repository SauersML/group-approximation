---
rg: 2
id: lifted-trace-matrix-divisibility-proof
kind: route
title: Trace the equivalent diagonal matrix units and use p-adic integrality
target: lifted-trace-bounds-unital-matrix-parts
requires:
  - lifted-trace-detects-finite-subgroup-projectives
  - leavitt-matrix-amplification-in-unit-group-algebra
---

Let f_ij be the images of the standard matrix units under a unital
map M_n(F_p)->eM_k(S)e. The f_ii are orthogonal idempotents with
sum e. Their right S-projectives are all isomorphic, implemented by
f_ij and f_ji. Therefore

    [eS^k]=n[f_11 S^k],
    a=n b,       b=t_p([f_11 S^k]) in Z_p.

This proves a in nZ_p. When a!=0, b!=0 and the nonnegative
valuation v_p(b) gives v_p(a)=v_p(n)+v_p(b)>=v_p(n).
If matrix blocks of unbounded p-power size exist with the same
identity, then a belongs to the intersection of p^r Z_p over all r,
which is zero. This step uses no compatibility between the blocks.

For the cubic idempotent e, the explicit lift (2-g-g^2)/3 has identity
coefficient 2/3, whose 2-adic valuation is one. The established
embedding j_2:M_2(S)->eSe sends I_2 to e, hence restricts to a unital
copy of M_2(F_2). The valuation bound forbids every size divisible by
four. A unital copy of M_4(S) would restrict to one of M_4(F_2), so
is likewise impossible.

For this example, the bound is visible already modulo four: after
lifting the diagonal idempotents and their equivalences through the
nilpotent coefficient ideal, four equivalent diagonal terms would
give T(E)=4T(F_11)=0, while the cubic lift E=2+g+g^2 has T(E)=2.

None of these arguments contradict an embedding with a smaller identity
E_n!=e. That is the changing-corner mechanism used by j_n.
