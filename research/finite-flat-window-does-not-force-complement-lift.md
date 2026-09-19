---
rg: 2
id: finite-flat-window-does-not-force-complement-lift
kind: claim
title: No finite flat compressed-coefficient window determines the SL3 complement unitary
distinct_from:
  macroscopic-zero-compressions-make-polar-data-universal: that makes all named compressions zero and hence leaves their polar factors arbitrary; this keeps every named compression uniformly invertible with a unique polar factor and still forbids a complement lift.
  canonical-exact-polar-models-have-flat-singular-loss: that has flat nonzero singular values but its polar tuple is one exact representation and therefore has no projective leak; this inserts one untested compressed coefficient which obstructs the complement while preserving canonical character and exact polar data on any prescribed finite window.
  canonical-fold-leak-is-complement-energy-or-h-singularity: that derives a complement-energy floor from a postulated fold leak; this constructs such a floor against any prescribed finite compression window, but does not construct a microstate of the full arithmetic double.
---

**ESTABLISHED FINITE-INCIDENCE FIREWALL.**  Put

```text
C=SL_3(Z) < A=SL_3(Z[1/2]).
```

Let `F` be any finite subset of `A\{1}` (in particular it may contain the
chosen presentation generators of `C` and every fixed finite SL3 incidence
word), and fix `0<t<1`.  There are exact finite-dimensional representations
`Pi_n:A->U(H_n)`, positive-density projections `P_n`, and unitaries
`U_n in U(P_n H_n)` such that:

1. `Pi_n` has canonical character on every fixed nonidentity word:

   ```text
   tr(Pi_n(g))->0                         (g!=1);       (FCI1)
   ```

2. every prescribed compression is uniformly nondegenerate and has a
   canonical exact polar factor:

   ```text
   P_n Pi_n(f) P_n = t rho_n(f),
   |P_n Pi_n(f)P_n|=tP_n,
   polar(P_n Pi_n(f)P_n)=rho_n(f)          (f in F),    (FCI2)
   ```

   where `rho_n:A->U(P_nH_n)` also has canonical character;

3. `U_n` commutes with every named polar factor in `(FCI2)` and has trace
   zero; but

4. there is **no** unitary `Z_n` on `(1-P_n)H_n` for which

   ```text
   U_n direct_sum Z_n in Pi_n(A)'.                       (FCI3)
   ```

Moreover one may choose one fixed `k in C` outside the prescribed window
and constants `epsilon_*>0`, `sigma_*>0`, independent of `n`, so that

```text
|P_n Pi_n(k)P_n| >= sigma_* P_n,
1-|tr([U_n,polar(P_nPi_n(k)P_n)])|^2 = epsilon_*,       (FCI4)
```

and consequently the optimized scaled complement energy on a fixed
generating set `S_C subset F` has a uniform floor:

```text
J_C(U_n) >= (sigma_*^2/(8K_k)) epsilon_*.               (FCI5)
```

Here `K_k` is the exact projective co-density transfer constant with target
`k`.  Thus neither canonical character, a positive retained density, unique
uniformly invertible polar factors, nor the flat value of **any fixed finite
list** of SL3 compressed coefficients constructs the complement unitary.

This includes every finite Stinespring/Gram shell, not only a list of
individual generators.  Given a finite word set `W`, apply the construction
with

```text
F=(W^(-1)W)\{1}.                                       (FCI5a)
```

Then every off-diagonal Gram coefficient between the spaces
`Pi_n(w)P_nH_n`, `w in W`, is the same flat coefficient
`t rho_n(w^(-1)v)`,
while the diagonal coefficient is the identity.  The induced action of
`U_n` is therefore isometric and consistent on that whole finite cyclic
shell.  It is the extension to all word depths which fails.

The exact positive criterion is preservation of the whole Stinespring
kernel.  For an exact representation `pi:G->U(H)`, a projection `P`, and
`U in U(PH)`, there is a block-diagonal lift

```text
Uhat=U direct_sum Z in pi(G)'                            (FCI6)
```

on the minimal cyclic dilation space if and only if

```text
U Ppi(g)P = Ppi(g)P U                 for every g in G. (FCI7)
```

Hence the complement variable is not mysterious: it is the commutant lift
of the **entire** compressed positive-definite kernel.  What fails is finite
local determination of `(FCI7)` from polar generator data.

This is not a canonical microstate countermodel for
`A *_C A`.  On the omitted word `k`, the polar of the raw compression is
not the product of the named generator polar factors.  Full-double
multiplicativity is exactly the extra joint condition absent here.  The
result therefore rules out constructing `Z` merely by enlarging a flat
finite coefficient/polar window at the exact-ambient compression level,
while leaving the regular arithmetic-double fold problem open.  It does not
rule out a genuinely cross-coefficient finite identity which already forces
the compression to reduce.
