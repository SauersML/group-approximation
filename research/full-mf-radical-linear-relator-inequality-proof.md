---
rg: 2
id: full-mf-radical-linear-relator-inequality-proof
kind: route
title: Glue the quadratic self-improvement to a corona compactness threshold
target: full-mf-radical-linear-relator-inequality
requires:
  - full-mf-radical-forces-perfect-commutator-bound
artifacts:
  - research/artifacts/mf-radical-linear-certificate-2026-09-07.md
---

## Proof

Take `W` and `B` from the prerequisite.

**Threshold.**  There are a finite set `R_0` of relations of `G` and
`delta>0` with `Def_(R_0)(U)<delta` implying `D(U)<=1/(2B)`.  Otherwise
enumerate the relations of `G` by finite exhausting sets
`R_1 subset R_2 subset ...` and pick `U^((n)) in U(d_n)^m` with
`Def_(R_n)(U^((n)))<1/n` and `D(U^((n)))>1/(2B)`.  Every fixed relation lies
in `R_n` for large `n`, so its defect tends to zero along the sequence, and
`x_i mapsto [U_i^((n))]_n` descends to a corona homomorphism
`G -> U(prod_n M_(d_n)/sum_n M_(d_n))`.  By the manuscript's MF residual
calculus that homomorphism is trivial, so `D(U^((n))) -> 0`, against the
choice.  The same threshold in the language of unitary-valued maps on the
group is the finite uniform form of
`full-mf-radical-uniform-asymptotic-collapse`; the derivation above is stated
for bare tuples so that no word section of `G` has to be chosen.

**Gluing.**  Put `R={r_1,...,r_s}=R_0 union W` and `C=max(2,2/delta)`.  If
`Def_R(U)<delta` then `D(U)<=1/(2B)`, and `(Q2)` gives
`D(U)<=2 Def_W(U)<=2 Def_R(U)`.  Otherwise `D(U)<=2<=(2/delta) Def_R(U)`,
using `||V-I||_op<=2` for unitaries.

**Converse.**  Let `phi:G->M` with `M` MF, and embed `M` in the unitary
group of a corona.  A lift `a` of a unitary satisfies
`a^*a-1 in sum_n M_(d_n)`, so after correcting finitely many coordinates `a`
is invertible in the finite von Neumann algebra `prod_n M_(d_n)`, and its
polar part is a unitary lift.  Lift `phi(g_i)` this way.  Each `r_j` is a
relation of `G`, so `||r_j(U^((n)))-I||_op -> 0`; then `(LIN)` forces
`D(U^((n))) -> 0`, which says `phi(g_i)=1` for every `i`.
