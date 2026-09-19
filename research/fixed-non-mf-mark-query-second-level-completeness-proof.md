---
rg: 2
id: fixed-non-mf-mark-query-second-level-completeness-proof
kind: route
title: Compile FIN by exact E switching and torsion-preserving Higman embedding
target: fixed-non-mf-mark-query-is-second-level-complete
requires:
  - exact-literal-e-fin-inf-switch
  - literal-central-mark-corona-invisible
artifacts:
  - GroupApproximation/Sofic/LiteralNonMFEndpoint.lean
---

Let

```text
E=<x_1,...,x_r | R_E>
```

be the literal forty-one-relator group and let `w=w(x_1,...,x_r)` be its
nontrivial central involution in its MF radical.  For a finite presentation
`p=<Y|S>`, define

```text
SURV_E,w(p)
  iff there are words u_1,...,u_r in F(Y) such that
      r(u_1,...,u_r)=1 in G_p for every r in R_E,
      w(u_1,...,u_r)!=1 in G_p.                         (EMQ1)
```

Equivalently, there is a homomorphism `phi:E->G_p` with `phi(w)!=1`.

## Upper bound

For finite presentations, the predicate

```text
Deriv(p,v,d) := d is a valid finite normal-closure derivation of v=1 in G_p
```

is decidable.  A witness for `(EMQ1)` consists of the tuple of target words
`u` and, because `R_E` is finite, one finite derivation certificate `c_r` for
each substituted relator.  Nontriviality of the substituted mark says that
no natural number is a derivation certificate for it.  Thus

```text
SURV_E,w(p)
 iff exists (u,c), forall d,
      [and_(r in R_E) Deriv(p,r(u),c_r)]
      and not Deriv(p,w(u),d).                          (EMQ2)
```

The matrix in brackets is decidable, so `SURV_E,w` is `Sigma^0_2`.  Its
complement `KILL_E,w`, saying that every homomorphism `E->G_p` kills `w`, is
`Pi^0_2`.

## Hardness

Use [[exact-literal-e-fin-inf-switch]] to compute a countably generated
recursive presentation `P_e` with value `E` when `W_e` is finite and value
`1` when `W_e` is infinite.  Apply Maurice Chiodo's uniform
torsion-order-preserving Higman compiler, Theorem 2.2 of *On torsion in
finitely presented groups* (Groups Complexity Cryptology 6 (2014),
arXiv:1107.1489).  It computes a finite presentation `T(P_e)`, an explicit
embedding

```text
P_e -> T(P_e),
```

and satisfies

```text
Tord(P_e)=Tord(T(P_e)).                                 (EMQ3)
```

If `W_e` is finite, the embedded copy of `E=P_e` retains `w`, so
`SURV_E,w(T(P_e))` holds.  If `W_e` is infinite, `P_e=1`, hence `(EMQ3)` says
that `T(P_e)` is torsion-free.  Since `w` has order two, every homomorphism
from `E` to `T(P_e)` kills `w`; therefore `KILL_E,w(T(P_e))` holds.  The
compiler is uniform, so this gives the many-one reductions

```text
FIN <=_m SURV_E,w,
INF <=_m KILL_E,w.                                     (EMQ4)
```

As `FIN` is `Sigma^0_2`-complete and `INF` is `Pi^0_2`-complete, `(EMQ2)`
and `(EMQ4)` prove the exact classifications.

## Why this is a non-MF certificate

The marked non-MF theorem is consumed here, not merely used to name an
interesting fixed group.  If `phi:E->G_p` retains `w`, functoriality of the
MF radical gives

```text
1 != phi(w) in Rad_MF(G_p).
```

Consequently every YES instance of `SURV_E,w` presents a non-MF group.  Thus
one fixed existential group constraint is a sound non-MF certificate and
recognizing whether it has a solution is already `Sigma^0_2`-complete; the
universal assertion that the certificate is impossible is `Pi^0_2`-complete.

This does not assert that all presentations in `KILL_E,w` are MF.  In
particular, torsion preservation makes the infinite branch torsion-free but
does not make it MF.  Therefore this theorem does not by itself close
`mf-recognition-finite-presentations-is-pi2-complete`.

