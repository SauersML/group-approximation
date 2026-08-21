---
rg: 2
id: iterated-leavitt-self-similarity-is-dual-prefix-matrix-chart
kind: claim
title: Iterated Leavitt self-similarity is exactly the dual-prefix matrix chart
artifacts:
  - research/artifacts/dual-prefix-leavitt-tower-integration-2026-08-21.md
distinct_from:
  leavitt-prefixes-form-exponential-heisenberg-packet: that applies the dual-prefix pairing to two Steinberg roots and obtains a common-sign finite Heisenberg group; this identifies the underlying ring isomorphism and all of its matrix units before groupification.
  relative-leavitt-active-subspaces-expand-by-two: that keeps only injectivity of the two forward branch maps on a finite coefficient space; this gives the full two-sided depth-n matrix equivalence, including every off-diagonal corner.
  leavitt-matrix-amplification-in-unit-group-algebra: that embeds matrix rings over the group algebra into a nonunital group-algebra corner; this is the unital active-corner self-similarity inside the relative Leavitt coefficient ring itself.
---

**ESTABLISHED.**  Let `R=L_A(S)` be a relative binary Leavitt envelope.  For
binary words `u=(u_1,...,u_n)` use the reversed dual-prefix convention

```text
t_u=t_(u_1)...t_(u_n),
s_u=s_(u_n)...s_(u_1).                                  (DPC1)
```

Then

```text
t_u s_v=delta_(u,v) A,
sum_(|u|=n) s_u t_u=A.                                  (DPC2)
```

On the active corner `ARA`, define

```text
Phi_n:ARA -> M_(2^n)(ARA),
Phi_n(r)_(u,v)=t_u r s_v,                               (DPC3)

Psi_n((r_(u,v)))=sum_(u,v) s_u r_(u,v) t_v.             (DPC4)
```

These are mutually inverse unital ring isomorphisms.  Moreover the prefix
corner words

```text
e_(u,v)=s_u t_v                                         (DPC5)
```

are a complete system of matrix units and

```text
Phi_n(e_(u,v))=E_(u,v),
Phi_n(A)=I_(2^n).                                       (DPC6)
```

Thus the exact pairing sometimes written `y_u x_v=delta_(u,v)A` is not a
new relation: with `y_u=t_u` and `x_v=s_v` it is precisely the diagonal
coefficient of the existing Leavitt self-similarity chart.

## Proof

The first equation in `(DPC2)` follows by cancelling the innermost letters;
the first mismatch gives `t_i s_j=0`.  The second follows by iterating
`s_0t_0+s_1t_1=A`.

For `r in ARA`, equations `(DPC2)` give

```text
Psi_n(Phi_n(r))
 =sum_(u,v) s_u t_u r s_v t_v
 =(sum_u s_ut_u) r (sum_v s_vt_v)=r.                   (DPC7)
```

Conversely, the `(a,b)` entry of `Phi_n(Psi_n((r_(u,v))))` is

```text
sum_(u,v) t_a s_u r_(u,v) t_v s_b=r_(a,b).             (DPC8)
```

The same cancellation gives

```text
e_(u,v)e_(w,q)=delta_(v,w)e_(u,q),
sum_u e_(u,u)=A,                                       (DPC9)
```

and `(DPC6)` follows by evaluating `(DPC3)` on `(DPC5)`.

## What the exact chart does and does not provide

Applying adjacent Steinberg roots to the row words `t_u` and column words
`s_v` turns `(DPC2)` into the common-sign Pauli tower already proved in
`leavitt-prefixes-form-exponential-heisenberg-packet`.  On a nontrivial
central phase its depth-`n` sector has dimension divisible by
`p^(2^n)`, and varying `n` annihilates the mark in every exact
finite-dimensional representation.

The isomorphism `(DPC3)` alone does not identify the same physical matrix
multiplicity reservoir before and after refinement.  In a finite matrix
model it permits the label factor to grow from `M_p` to `M_(p^2)` while the
spectator multiplicity shrinks, exactly as in `rectangular-escape`.  The
remaining `Phi` target is therefore not another algebraic pairing identity:
it is the matrix-coordinate same-corner assertion in
`paired-same-reservoir-boundary-lemma`.  At the first binary step,
`four-pauli-standard-polynomial-gives-a-fixed-rectangular-gap` gives the
explicit `s4` contradiction as soon as the same returned four Pauli words
are simultaneously target-Pauli and confined to the recovered source
`M_2` factor.
