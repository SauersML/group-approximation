---
rg: 2
id: canonical-moments-linearize-fixed-depth-fanizza-return
kind: claim
title: Canonical word moments linearize every fixed-depth Fanizza scalar return
distinct_from:
  scalar-trace-reflection-is-julia-root-target: that identifies the trace mismatch as the minimum unconditional finite-coordinate payload; this shows that under canonical-delta side conditions the mismatch is already a finite linear word-moment functional.
  canonical-profile-collapse-compactness: that obtains non-effective finite windows from qualitative collapse; this gives an explicit finite window and linear constant once one regular canonical-trace inequality is known.
  fanizza-heat-return-is-one-cyclic-amplitude-product: that derives the scalar comparison from two matrix products and cyclicity; this derives it directly from canonical word moments and needs no returned products.
---

**ESTABLISHED.**  Let `Gamma=<S|R>` be finitely or recursively presented,
and let `P,A in Q[F(S)]` have finite support, with `A=A^*`.  Put

```text
q=P^*P-A=sum_(j=1)^M c_j v_j.                         (CMF1)
```

If the canonical group trace satisfies

```text
tau_Gamma(P^*P)<=tau_Gamma(A)+b,                      (CMF2)
```

then there are a finite relator prefix `R_0`, a finite window `F_0` and a
finite constant `C_q` such that every matrix tuple `U` satisfies

```text
||P(U)||_2^2
 <=tr(A(U))+b+C_q(def_(R_0)(U)+sep_(F_0)(U)).         (CMF3)
```

Here `F_0` contains the nonidentity images among the finitely many `v_j`, and
`sep` measures their deviation from canonical trace zero.  Thus, for the
Fanizza amplitude `A=A_(m,t)`, the regular inequality with `b=0` implies the
entire depth-`t` return estimate `(DFR1)`.  The constant may depend
arbitrarily on `t` through the coefficient mass and the finitely many word
areas.

## Proof

Partition the indices in `(CMF1)` according to whether `v_j=1` in `Gamma`.
For each identity word choose one finite derivation from relators, and let
`R_0` contain all relators occurring in those finitely many derivations.
Telescoping gives

```text
|tr(v_j(U))-1|<=L_j def_(R_0)(U)       when v_j=1,    (CMF4)
```

for finite `L_j`.  For every remaining `v_j`, put it in `F_0`, so

```text
|tr(v_j(U))|<=sep_(F_0)(U).                           (CMF5)
```

Since the canonical trace is `1` on the first class and `0` on the second,

```text
|tr(q(U))-tau_Gamma(q)|
 <=sum_(v_j=1)|c_j|L_j def_(R_0)(U)
   +sum_(v_j!=1)|c_j|sep_(F_0)(U).                    (CMF6)
```

Take `C_q` larger than the two displayed coefficient sums and use
`tau_Gamma(q)<=b`.  Finally
`tr(P(U)^*P(U))=||P(U)||_2^2` exactly, proving `(CMF3)`.

## Consequence for the proposed decoders

Under canonical-profile conditioning, neither a cyclic pair `X,Y`, an
additive commutator, nor the `2 by 2` Julia projection is needed **after**
`(CMF2)` is available.  Conversely, along any canonical microstate sequence,
every proposed scalar return converges to `(CMF2)`.  Hence these block
packages cannot improve the canonical scalar endpoint; their only possible
role is to prove the regular trace inequality algebraically.

An ordinary word cannot secretly name the Julia group-algebra contraction.
Distinct group elements are orthonormal in `L^2(L(Gamma),tau_Gamma)`, so if
`a=sum_g a_g g` has combined group support and `w in Gamma`, then

```text
||w-a||_(2,tau)^2=1+sum_g |a_g|^2-2 Re(a_w).          (CMF7)
```

It vanishes only when `a=w`.  Thus adjoining a wandering word or Julia word
does not create the needed comparison merely by canonical support; a
genuine group-algebra relation or canonical trace inequality remains
necessary.

