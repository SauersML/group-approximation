---
rg: 2
id: parity-exact-double-pauli-is-stationary-for-intrinsic-green-step
kind: claim
title: An exact covered parity tuple can be stationary for the intrinsic Green step
distinct_from:
  clifford-packets-are-stationary-for-intrinsic-green-step: that uses a fully pairwise-anticommuting packet without parity constraints; this gives a positive-distance code tuple in which every coordinate lies in an exact commuting parity face.
  parity-exact-shared-contractions-have-intrinsic-cp-gap: that proves a pre-character spectral gap for the coordinate CP channel and the correct linear contraction at exact commuting code tuples; this shows the gap does not imply nonlinear off-base coercivity even when all of its local exactness and sharing hypotheses hold.
  sparse-pauli-pair-defeats-random-order-blr: that concerns ordered-product BLR and permits parity defects on the two bad coordinates; this has zero parity and equality defect and evaluates the intrinsic finite-Green map itself.
---

ESTABLISHED SHARP RESTRICTED COUNTERMODEL.  Let

```text
 C={(a,a,b,b):a,b in F_2} subset F_2^4.                (PED1)
```

This binary code has relative distance `1/2`; its two parity faces are
`{1,2}` and `{3,4}`, so every coordinate belongs to an exact bounded face.
On one qubit choose anticommuting Pauli reflections `A,B` and set

```text
 Q_1=Q_2=A,       Q_3=Q_4=B.                           (PED2)
```

The tuple is literally shared.  Each parity face is commuting and has
product `I`, and every equality copy may be chosen identical.  Nevertheless
the tuple is globally noncommuting and is an exact fixed point of the
intrinsic finite-Green map `(IFG1)--(IFG4)` for every depth `K`:

```text
 F_K(Q)=Q.                                              (PED3)
```

Indeed, for each `i`, exactly two of the four `Q_j` anticommute with `Q_i`.
Thus

```text
 beta_ij=(I-(Q_iQ_j)^2)/2
          =0  on the same Pauli pair,
          =I  on the opposite Pauli pair,

 c_i=(1/4)sum_j beta_ij=(1/2)I.                        (PED4)
```

Every current pinching fixes this scalar.  Therefore the Green output
`g_i=G_(Q,K)c_i` is selfadjoint, its skew part `k_i` is zero, and `(PED3)`
follows.  The normalized ordered-pair energy is

```text
 E_pair=(1/16)sum_(i,j)||[Q_i,Q_j]||_2^2=2.            (PED5)
```

Hence exact local parity, exact equality sharing, positive code distance,
and a uniform spectral gap of the intrinsic coordinate CP channel do not
imply a global Polyak--Lojasiewicz inequality or strict nonlinear residual
contraction.  The CP-gap theorem remains correct: it controls the derivative
at the exact **commuting** locus, whereas `(PED2)` is a remote critical point.

Central trace dilution again makes total normalized HS energy arbitrarily
small without changing the fixed-point calculation.  This still does not
defeat the retained diffuse route.  For an anchor in the `A` pair, precisely
the two `B` coordinates have odd square equal to `I`, and conversely, so

```text
 K_a=(1/4)sum_i Y_(a,i)^2=(1/2)I.                      (PED6)
```

Every regularized aggregate threshold below `1/2` removes the whole bad
block.  Thus the strongest valid restricted statement needs **both** exact
shared parity and the retained low-anchor-square-function hypothesis.  Local
exactification and literal sharing alone do not close off-base coercivity.
