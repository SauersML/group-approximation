---
rg: 2
id: stw61-circle-properly-infinite-coefficient-maximal-commutator
kind: claim
title: Arbitrary circle and properly infinite coefficient products obey the enlarged Fock commutator obstruction
distinct_from:
  stw61-mixed-semicircular-maximal-commutator: This adjoins the circle generator and unrestricted complementary coefficient isometries, including a whole unital properly infinite T2 copy, and proves exact distance one-half from the missing projection.
artifacts:
  - research/artifacts/stw61-circle-and-properly-infinite-coefficient-fock-obstruction-2026-09-05.md
---

For n>=2, in the full unital free product C_n=C(S1)*T_n put

```text
p=v_1v_1*,  e_n=1-sum_i v_i v_i*,
K_n=C*(1,z,v_2,...,v_n,zv_1+v_1*z*).
```

Then ||[z,WpW*]||=1 for every W in U(K_n). The norm distances
dist(p,K_n), dist(e_n,K_n), and dist(WpW*,K_n) all equal 1/2.
Both WpW* and its complement are properly infinite and full.

In the original C=C(S1)*T2, this gives the same maximal-norm
theorem for every unitary in

```text
K=C*(1,z,s_2s_1,s_2s_2,zs_1+s_1*z*),
p=s_1s_1*.
```

The coefficient algebra C*(1,s_2s_1,s_2s_2) is a faithful unital
properly infinite T2 copy. Arbitrary coefficient unitaries,
independent circle functions, mixed self-adjoint operations,
and further unitary functional calculus within K are allowed.
Here dist(p,K)=dist(e+s_2 e s_2*,K)=1/2.

The explicit exponential family from the preceding semicircular
claim lies in this class and escapes every proper original
coefficient corner. Nevertheless K is a proper subalgebra: its
exact distance from p prevents even approximation of that
additional coefficient. The statement does not cover every
unitary of C and does not settle LXI.

ROUTES

stw61-enlarged-fock-commutant-proof
