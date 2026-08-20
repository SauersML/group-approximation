---
rg: 2
id: oriented-c18-rank-gates-give-branch-balance
kind: claim
title: Two oriented C18 rank gates give exact active-plus-exit branch balance
artifacts:
  - experiments/fanizza_oriented_c18_exit_compiler.py
distinct_from:
  fanizza-final-bcs-has-fixed-nonlinear-menu: that records C18's 20 forbidden assignments as one Boolean constraint; this replaces them, only on the forward source carrier, by 20 oriented exit occurrences counted with multiplicity.
  binary-cut-projection-recurrence-gives-bfe1: that converts a supplied projection recurrence residual into a scalar balance; this proves the required balance pointwise on the C18 spectral atoms after packet replacement.
  fanizza-bad-atoms-have-symmetric-frames: that builds one frame for each original forbidden atom; this recompiles the recurrence into two oriented predicates and obtains a common hard root without a coordinate swap.
---

Write the first three C18 projection bits as `(p,q,r)` and let `h` be the
indicator that the last three sign bits have even parity.  Define two Boolean
exit predicates

```text
e_1 = h [p+q-r>0],
e_2 = h [(p,q,r)=110].                                 (OCB1)
```

On the phase-even carrier, the following **integer**, not mod-two,
inequalities hold pointwise:

```text
p+q <= r+e_1+e_2,
e_1+e_2 <= p+q.                                        (OCB2)
```

The factor of two in this ledger is essential.  Let `mu` be any joint
spectral measure for which `int p dmu=int q dmu=q`, put

```text
s=int(e_1+e_2)dmu,
a=s/2,                 x=s/2,
q_next=int r dmu+a.                                       (OCB2a)
```

Here each oriented rank jump is split into its equal relative-Pauli active
half and exit half.  Integrating `(OCB2)` gives

```text
2q <= q_next+x,        x<=q.                              (OCB2b)
```

Thus `(OCB2b)` is exactly `(BFE1)--(BFE2)` at the scalar multiplicity scale.
Counting the whole rank-jump block as an exit would violate `(BFE2)`; counting
only its exit half without adding the active half to `q_next` would violate
`(BFE1)`.

At the double-source atom `110`, both oriented occurrences fire; at `111`
only one fires.  The only original C18 bad atom not seen by `e_1` is `001`,
which has `p+q=0` and therefore zero intersection with the forward source
carrier.  More precisely, if

```text
f_C18=h[p+q!=r],       s=[p+q>0],
```

then

```text
f_C18 s=e_1.                                           (OCB3)
```

Thus the corner-localized C18 forbidden mass on the source carrier is exactly
the first oriented exit mass, while `e_2` supplies the second unit required
by the size-two residual at `110`.

The oriented truth tables have `16` and `4` atoms.  Their optimized OBDD
Schur compilers have baseline ranks `10` and `9`, hence matrix sizes `11` and
`10`, both smaller than the size-12 compiler for undirected C18.  Every one
of the 20 oriented occurrences admits a weight-at-most-two source-fixed frame
with

```text
K_sym=span{e_01,e_23,e_03+e_12},
hard form=e_02^*,
reverse coefficient sign J=+1.                         (OCB4)
```

So the two exits enter the same E5 top root directly.  The total number of
rank-one exit occurrences remains 20: removing the four source-free `001`
atoms and counting the four `110` atoms twice preserves the finite budget.

The exit halves can be packed into one source copy without overlap.  In the
product of the two oriented packets let `F_i` be the central support of
`e_i`, and let `Q_1` be one named relative Pauli involution for the first
gate.  Since `F_2<=F_1`,

```text
X_1=F_1(I-Q_1)/2,       X_2=F_2(I+Q_1)/2               (OCB5)
```

are orthogonal.  Pauli trace balance gives
`tau(X_i)=tau(F_i)/2`, so `tau(X_1+X_2)=s/2<=q`.

This is an oriented recurrence compiler, not an equivalent replacement of
C18 on arbitrary corners.  Its use is valid precisely after cutting to the
forward source carrier, where `(OCB3)` retains the full C18 soundness mass.
The scalar balance and source packing do not by themselves place the active
halves at the next clock level; that finite group-word transport remains a
separate presentation-level obligation.
