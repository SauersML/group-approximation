---
rg: 2
id: julia-colligation-is-neutral-to-the-asynchronous-mirror-exit
kind: claim
title: The Julia colligation is exactly neutral to the finite mirror exit of an unequal-prefix shift
distinct_from:
  inside-corner-hecke-tests-miss-the-asynchronous-mirror-exit: that proves arbitrary source-corner coefficients cannot see the complement mirror; this tests the smallest nonlinear Julia/Halmos enlargement and computes both defect blocks.
  fano-uncovered-ghost-energy-is-one-julia-commutator: that packages a prescribed leakage contraction into a Julia reflection; this shows that merely naming the reflection does not authenticate which off-diagonal block is the prescribed contraction.
  universal-block-return-violates-the-regular-firewall: that rules out fixed universal proper-corner products by regular trace; this gives an exact finite counterpacket satisfying every Julia unitary identity while retaining positive oriented source defect.
  one-sided-amitsur-oracle-has-two-unitary-corner-model: that uses a Halmos dilation only to provide exact infinite completeness for a matrix polynomial oracle; this audits the proposed use of the dilation itself as a finite-HS soundness cell.
---

Let `E` be a projection, let `T` be a unitary, and compress the proposed
unequal-prefix shift to

```text
A=ETE in EME.                                           (JCM1)
```

Put

```text
D_in=(E-A^*A)^(1/2),          D_out=(E-AA^*)^(1/2),
J_A=[[D_in, A^*],
     [A,   -D_out]]                                    (JCM2)
```

on `EH direct-sum EH`.  The defect-operator identity
`A D_in=D_out A` makes `J_A` a self-adjoint unitary for **every** contraction
`A`.

In the exact infinite unequal-prefix model, choose `TE<=E` with proper range
`F=TET^*<E` and put `H=E-F`.  Then

```text
A^*A=E,             AA^*=F,
D_in=0,             D_out=H.                           (JCM3)
```

Thus the initial/source defect vanishes exactly while the marked exit `H`
survives, which is the desired Hilbert-hotel orientation.

The finite mirror counterpacket has indistinguishable Julia syntax.  Take
`E=F+H`, choose `C<=1-E` with `rank(C)=rank(H)`, and let `T` fix `F` and
swap `H` with `C`.  Then

```text
TET^*=F+C,             A=ETE=F,
D_in=H=D_out,                                      (JCM4)
```

so

```text
J_A^*=J_A,             J_A^2=1,
tr(D_in^2)=tr(H)>0.                                  (JCM5)
```

Every Julia/Halmos colligation relation has zero defect, yet the oriented
source-Gram defect is macroscopic.  By
`inside-corner-hecke-tests-miss-the-asynchronous-mirror-exit`, arbitrary
finite D8/Hecke coefficients supported in `E` also take exactly their
intended proper-range values.

Consequently no dimension-independent inequality

```text
tr(E-A^*A)
 <= C( ||J_A^2-1||_2^2+||J_A-J_A^*||_2^2
       +inside-corner packet defects )                 (JCM6)
```

can hold.  The right side is zero in `(JCM4)` and the left side is
`tr(H)>0`.

The result also identifies the minimum surviving correlation.  A group-word
packet may name a literal involution `j` playing the role of `J_A`, but
unitarity of `j` is vacuous for orientation.  It must additionally
authenticate that the **specific** upper-left defect block is `D_in=0`, or
equivalently that the lower-left block has source Gram `E`.  That is exactly
the finite-matrix source-Gram decoder; it is not supplied by Julia/Halmos
functional calculus or by an unequal-prefix partial shift alone.
