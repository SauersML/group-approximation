---
rg: 2
id: prime-cyclic-cancellation-lifts-force-reverse-inverses
kind: claim
title: Prime cyclic cancellation lifts force reverse inverses with an exact scalar lattice criterion
distinct_from:
  central-sign-survival-forces-reverse-cancellation: that treats characteristic two with paired cells and a central involution; this handles every prime using coefficient multiplicities, blocks of p cells, and a central element of order p.
  cyclotomic-liftable-cancellation-pairs-have-no-inverse-defect: that tests a constant parity character on binary pairings; this tests a labelled character modulo any prime and exhibits a characteristic-three template requiring ninth roots.
artifacts:
  - research/artifacts/kaplansky-prime-cyclic-cancellation-2026-09-07.md
  - experiments/kaplansky_prime_cancellation.py
  - research/artifacts/kaplansky-prime-cancellation-c3.json
---

Fix a prime p and BA=1 in F_p[G]. Expand each nonzero coefficient c
into c occurrences, using its representative in {1,...,p-1}. Write
B=sum_i[t_i], A=sum_j[s_j] with these occurrence lists; repetitions
of group labels are allowed and retain separate coefficient variables.

Choose one identity-product cell as pivot and partition all remaining
product occurrences into ordered p-tuples of equal group product. Such
a partition exists. Number the pivot (0,0). For each block use cell 0
as base and label its other cells by a=1,...,p-1. Define H by

    J^p=1, J central, X_0=Y_0=1,
    X_(i_a) Y_(j_a) = J^a X_(i_0) Y_(j_0)

for each labelled cell in every block; block subscripts are local and
the globally distinguished pivot lies in no block.

If J!=1 in H, then AB=1. Thus a strict one-sided inverse forces J=1
for every permitted occurrence partition, ordering and pivot. An exact
equivalent obstruction is an identity among conjugates of the unsigned
relators whose signed sum of labels is nonzero modulo p. Asphericity
of this particular unsigned presentation is sufficient to retain J.

There is a decidable sufficient scalar criterion. Let V have columns
v_e=e_(i_a)+f_(j_a)-e_(i_0)-f_(j_0), and let ell_e=a. Then scalar
p-power phases exist if and only if

    V u=0 in Z^(m+n) implies ell dot u=0 mod p
    for every integral vector u.

Equivalently, for some N>=1 the finite congruence

    V^T q = p^(N-1) ell mod p^N

has a solution. Such a solution forces AB=1. If r=rank_Q(V)>0 and d_r
is the largest nonzero Smith invariant, N<=1+v_p(d_r) suffices. In
particular one may take N<=1+floor(log_p(2^r)), and r<=m+n-2.
The bound uses occurrence counts,
not just the sizes of the distinct supports.

The attached F_3[C_3] example has no cube-root phases for its specified
ordered blocks but has explicit ninth-root phases. It is a two-sided
inverse example, not a counterexample to Kaplansky's conjecture.

This is a conditional exclusion theorem. No assertion is made that every
inverse pair admits a partition with surviving J, or that J collapse
implies a reverse defect. The general conjecture remains unresolved.
