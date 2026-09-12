---
rg: 2
id: sequential-corner-trace-deficiency-proof
kind: route
title: Sum complementary polar deficiencies once against the final block unitary
target: sequential-exact-corner-extraction-has-quadratic-error-ledger
requires: []
artifacts:
  - research/artifacts/microscopic-schreier-extraction-dimension-ledger-2026-09-05.md
---

Fix a generator and abbreviate U_s^(i) to U_i. Let Q_i=I-P_i on the
current remaining space, and put
`E_i=U_(i+1)-Q_i U_i Q_i`. If the compression's singular values are
s_l in [0,1], the unitary polar completion satisfies

```text
||E_i||_1=sum_l(1-s_l)<=sum_l(1-s_l^2)
 =||P_i U_i Q_i||_HS^2=||Q_i U_i P_i||_HS^2
 <=xi_i^2 r_i.                                        (SET1)
```

Equality of the two off-diagonal HS masses follows from unitarity.
The last inequality uses the off-diagonal part of `(SEL1)`. The same
retained-column estimate, expanded as a squared distance between two
isometries from P_i H_i, gives

```text
Re Tr(rho_i(s)^*P_i U_i P_i)>=r_i-xi_i^2 r_i/2.         (SET2)
```

Let R_i be projection onto H_i in the original coordinates. Repeated
compression gives

```text
U_i=R_i U_0 R_i+sum_(l<i) R_i E_l R_i
```

as operators on H_i, where the E_l are extended by zero. Evaluate the
diagonal overlap of the final block unitary V_s with U_0. In each
extracted block use `(SET2)`, and in the final remaining block use the
overlap of U_N with itself, namely dim H_N. For each l, all appearances
of E_l are paired with the direct sum of the later final blocks on
H_(l+1). That direct sum is a unitary, so the absolute value of this
entire contribution is at most ||E_l||_1, once. There is no factor for
the number of later blocks. Thus

```text
Re Tr(V_s^*U_0)
 >=d-(1/2)sum_i xi_i^2 r_i-sum_i ||E_i||_1
 >=d-(3/2)sum_i xi_i^2 r_i.
```

Both V_s and U_0 are unitary. Expanding their squared HS distance
proves `(SEL2)`. If the final block is instead identity, its overlap
with U_N is at least -dim H_N rather than dim H_N. The loss in real
overlap is at most twice that dimension. The same calculation proves
`(SEL3)`. The resulting tuple is exact since it is a direct sum of the
exact rho_i and a trivial representation. Every step is finite; no
convergence or exact-reducing assumption has been inserted.
