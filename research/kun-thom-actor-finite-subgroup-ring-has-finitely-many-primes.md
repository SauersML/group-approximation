---
rg: 2
id: kun-thom-actor-finite-subgroup-ring-has-finitely-many-primes
kind: claim
title: The finite-subgroup ring of a Kun--Thom Theorem E actor inverts only finitely many primes
distinct_from:
  leavitt-unit-group-contains-every-finite-group: that embeds every finite group in L^x, so the Leavitt unit group's finite-subgroup ring is Q; this shows the Kun--Thom actors behave the opposite way, with finite subgroups involving only finitely many primes.
  kun-thom-actors-have-no-torsion-free-finite-index-subgroups: that produces elements of order p in every finite-index subgroup of the actors; this bounds the set of all primes that divide orders of finite subgroups.
---

**ESTABLISHED.** Let `q = p^f`, `r, d >= 3`,
`R = F_q[x_1^(+-1), ..., x_d^(+-1)]`, and `G = EL_r(R) semidirect SL_d(Z)`,
the actor of a Kun--Thom Theorem E pair. Every prime dividing the order of a
finite subgroup of `G` lies in the finite set

```text
P(q,r,d) = {p}  union  {l : l divides q^k - 1 for some 1 <= k <= r}  union  {l : l <= d + 1}.
```

Hence

```text
Lambda^G = Z[ 1/|H| : H <= G finite ]  is contained in  Z[ 1/l : l in P(q,r,d) ],  a proper subring of Q.
```

**Why it matters for Baum--Connes.** For `L^x` the trace test is void:
`leavitt-unit-group-contains-every-finite-group` gives `Lambda^(L^x) = Q`.
For the Kun--Thom actors it is live. Lück (Invent. Math. 149 (2002);
literature context, not imported here) confines traces of reduced assembly
images to `Lambda^G`. So for a Theorem E actor, any of the following would
refute surjectivity of `mu_r`:
- a projection in some `M_n(C*_r G)` with trace `1/l` for a prime `l` not in
  `P(q,r,d)`;
- more generally, any projection whose trace lies outside
  `Z[1/l : l in P(q,r,d)]`, irrational traces included.

Nothing in the graph produces such a projection. Subgroup averages give values
in `Lambda^G`, and Kazhdan projections vanish in `C*_r G`
(`subgroup-average-projections-give-no-reduced-bc-obstruction`). See
`baum-connes-counterexample-group-exists`.
