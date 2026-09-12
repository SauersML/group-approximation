---
rg: 2
id: mikhailova-fiber-product-gives-regular-mf-benign-compiler
kind: claim
title: Mikhailova fiber products give a uniform regular-MF benign compiler
distinct_from:
  positive-benign-compiler-specializes-to-kernel-witness: that asks the witness data themselves to specialize to one fixed graph witness; this construction works for every recursively enumerable normal subgroup and keeps only its ambient group, not its marked subgroup, uniformly residually finite.
---

**ESTABLISHED.**  Let `F=F(A)` be a finite-rank free group and let
`N_e normal F` be a uniformly recursively enumerable family.  There is a
total uniform construction of a benign witness

```text
(K_e, i_e:F->K_e, L_e<=K_e)                                   (MBC1)
```

such that `K_e` is a finite direct product of finite-rank free groups, `L_e`
is finitely generated, `i_e` is injective, and

```text
i_e(F) intersect L_e = i_e(N_e).                              (MBC2)
```

In particular every `K_e` is finitely presented, residually finite, and
regularly operator-MF realized.  The regular-MF conclusion holds on every
branch; it does not require recognizing a positive specialization.

## Construction

Apply the effective Higman embedding theorem to `Q_e=F/N_e`.  It returns a
finite presentation

```text
H_e=<X_e | R_e>
```

and words `w_a in F(X_e)` whose values give an embedding `Q_e->H_e`.  Let

```text
M_e=< (x,x), (r,1) : x in X_e, r in R_e >
       <= F(X_e) times F(X_e).                                (MBC3)
```

Mikhailova's fiber-product calculation gives

```text
M_e={(u,v): u and v have the same value in H_e}.               (MBC4)
```

Now put

```text
K_e=F(A) times F(X_e) times F(X_e),
i_e(a)=(a,w_a,1),
L_e=F(A) times M_e.                                           (MBC5)
```

The first coordinate makes `i_e` injective.  For `f in F`,

```text
i_e(f) in L_e
 iff (w_f,1) in M_e
 iff w_f=1 in H_e
 iff f in N_e,                                                (MBC6)
```

which proves `(MBC2)`.  Every displayed generating set and presentation is
finite and is computed directly from the effective Higman output.
