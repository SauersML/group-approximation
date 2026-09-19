---
rg: 2
id: partitioned-child-surplus-collision-supplies-contraction
kind: claim
title: A partitioned family of child returns supplies strict contraction without an aggregate reflection
distinct_from:
  tail-wordized-child-surplus-collision-supplies-rct7: That uses one aggregate corrected-child projection and one carrier reflection; this replaces it by finitely many source pieces and an orthogonal partition of the next carrier.
  five-fourths-projection-surplus-pays-linear-hs-energy: That charges one fixed local capacity surplus; this derives the recurrent Schur contraction inequality from an arbitrary finite child-surplus family.
  aggregate-child-wordization-three-route-no-go: That rules out three constructions of one aggregate child word; this proves that no aggregate word is analytically necessary.
---

**ESTABLISHED ANALYTIC BYPASS.**  Let `(M,tr)` be a normalized finite
matrix algebra.  At level `n`, let

```text
Q_n                         current baseline carrier,
C_(n,0),...,C_(n,m)         returned child pieces,
D_(n+1,0),...,D_(n+1,m)     pairwise orthogonal target pieces,
Q_(n+1)>=sum_i D_(n+1,i).                              (PCS1)
```

The `C_(n,i)` need not commute and need not be mutually orthogonal.  Put

```text
a_n=tr(Q_n),       a_(n+1)=tr(Q_(n+1)),
ell_(n,i)=||(1-D_(n+1,i))U_(n,i)C_(n,i)||_2^2          (PCS2)
```

for arbitrary unitary returns `U_(n,i)`.  If

```text
sum_i tr(C_(n,i)) >= a_n+v_n-xi_n,                    (PCS3)
v_n >= beta a_n-delta_n,          beta>0,             (PCS4)
```

then

```text
(1+beta)a_n
 <= a_(n+1)+delta_n+xi_n+sum_i ell_(n,i).             (PCS5)
```

Consequently

```text
a_n <= lambda a_(n+1)
       +lambda(delta_n+xi_n+sum_i ell_(n,i)),
lambda=(1+beta)^(-1)<1.                               (PCS6)
```

This is the strict recurrence consumed by
`contractive-computation-ladder`.  It requires neither a projection equal to
`sum_i C_(n,i)` nor a word for its reflection.  In particular, source pieces
belonging to different noncommuting BCS contexts may be kept separate.

For each `i`, traciality gives the exact capacity estimate

```text
ell_(n,i)
 =tr(C_(n,i))-tr(D_(n+1,i)U_(n,i)C_(n,i)U_(n,i)^*)
 >=tr(C_(n,i))-tr(D_(n+1,i)).                         (PCS7)
```

Sum `(PCS7)`, use orthogonality in `(PCS1)`, then substitute
`(PCS3)--(PCS4)` to obtain `(PCS5)`.

If the individual source and target reflections are ordinary words,
`unitary-offdiagonal-block-gram-is-support-leakage` bounds every
`ell_(n,i)` by one conjugacy-relator energy.  More generally, a fixed finite
subgroup/type chart may control the same leakage by finite-table
exactification and polar alignment.  Since the number of pieces is fixed,
polynomial word cost still gives

```text
delta_n+xi_n+sum_i ell_(n,i) <= C p(n)sqrt(E),         (PCS8)
```

and the established contraction ladder yields a dimension-independent
energy floor from any positive level-zero marked mass.

## Exact scope

This removes the **aggregate-word** obstruction and nothing more.  A group
construction must still do three things on one shared BCS tuple:

1. expose finitely many genuine child pieces satisfying `(PCS3)`;
2. place their returned targets in one orthogonal partition `(PCS1)` with
   leakage paid as in `(PCS8)`; and
3. retain an exact infinite completion in which the mark survives.

Those obligations are recorded by
`typewise-schur-tail-partition-compiler`.  Unlike a trace-functorial
first-hit ladder, `(PCS5)` is allowed to use the finite-matrix-only robust BCS
surplus `(PCS4)`; the perfect infinite completion has `v_n=0`.

