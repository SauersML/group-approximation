---
rg: 2
id: binary-leavitt-canonical-morita-tree-reduction
kind: claim
title: A canonical Morita branch tree reduces the Leavitt chromatic compiler to one first-mismatch area cell
distinct_from:
  binary-leavitt-cumulative-complete-graph-table: that obtains a diagonal pairing by a growing triangular change of basis; this uses the fixed two stabilized Morita branch words and makes every diagonal discrepancy a literal conjugate of one base cell.
  stabilized-morita-branches-are-inner-but-incoherent: that audits global normalized-Hilbert--Schmidt frame synchronization and fixed-sign comparison; this uses the vertex-dependent conjugate signs allowed by the operator-norm chromatic criterion and isolates only the cross-branch filling.
  binary-leavitt-first-mismatch-morita-area-cell: that asks for the remaining uniform filling; this proves that that single estimate supplies complete graphs of unbounded order with no further coherence hypothesis.
artifacts:
  - research/binary-leavitt-bounded-area-chromatic-code.md
---

**ESTABLISHED REDUCTION.**  Work in a fixed finite presentation of the
stabilized binary-Leavitt Steinberg group.  Let `D_0,D_1` be the two fixed
inner Morita branch words of
`stabilized-morita-branches-are-inner-but-incoherent`, and choose base words

```text
c=x_12(AE_11),       h=x_23(AE_11),       z=x_13(AE_11).       (MTR1)
```

For a binary word, define

```text
D_empty=1,                 D_(iu)=D_iD_u,
c_u=D_ucD_u^(-1),          h_u=D_uhD_u^(-1),
z_u=D_uzD_u^(-1).                                         (MTR2)
```

There is a constant `A_Delta`, independent of `u`, such that

```text
Area([c_u,h_u]z_u^(-1))<=A_Delta.                         (MTR3)
```

Indeed the word on the left freely reduces to the conjugate by `D_u` of the
one base discrepancy `[c,h]z^(-1)`.

Suppose, in addition, that there is one constant `A_times` such that for all
binary tails `a,b` and unequal bits `i!=j`,

```text
Area([c_(ia),h_(jb)])<=A_times.                           (MTR4)
```

Then `binary-leavitt-bounded-area-chromatic-code` holds.  At depth `n`, use
the complete graph on `{0,1}^n` and the words `(c_u,h_u,z_u)`.  If `u!=v`,
write

```text
u=pia,                 v=pjb,                 i!=j.       (MTR5)
```

The off-diagonal discrepancy freely reduces to the conjugate by `D_p` of
`[c_(ia),h_(jb)]`, so `(MTR4)` gives the same area bound on every edge.
The complete graphs have chromatic numbers `2^n`, while `(MTR3)` gives the
diagonal clause with the permitted conjugator `a_u=D_u`.  Thus the bounded
chromatic criterion applies with constants independent of depth.

The coefficient calculation behind the remaining cell is exact.  If the
tail coefficients represented by `c_a,h_b` are `r_a,s_b`, then `(SMI2)`
gives

```text
c_(ia)=X(r_a t_i E_11),       h_(jb)=Y(s_j s_b E_11),
r_a t_i s_j s_b=0                         for i!=j.       (MTR6)
```

Thus all address depth beyond the first mismatch occurs only as a left and a
right coefficient context around the single defining ring relation
`t_i s_j=0`.  No pair-dependent transporter or stabilizer comparison remains
in the vertex definitions.

The reduction does not identify exact context absorption with bounded area.
That quantitative comparison is precisely
`binary-leavitt-first-mismatch-morita-area-cell`.
