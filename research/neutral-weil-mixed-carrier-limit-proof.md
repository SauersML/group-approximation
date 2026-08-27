---
rg: 2
id: neutral-weil-mixed-carrier-limit-proof
kind: route
title: Evaluate the two rounded words in the signed projective-line carrier
target: neutral-weil-mixed-carrier-energy-tends-to-355-over-64
requires:
  - neutral-weil-symmetric-retraction-is-double-neutral
  - deleted-fixed-line-first-cubic-has-explicit-positive-spectrum
  - even-weil-two-cubic-exit-angle-is-one-over-root-p-plus-two
---

Put `a=p^(-1/2)`.  The usual coherent vectors obtained from the deleted
vector `q=delta_0` are indexed by the projective line.  On every fixed
finite set of distinct rational points their Gram matrix tends to the
identity: every off-diagonal entry is a normalized nondegenerate quadratic
Gauss sum and hence has modulus at most `a`.  Reduction modulo `p` is
injective on the finite set below once `p` is large.

The one-line polar formula and the rank-two carrier calculation give the
following limiting model on
`ell^2(P^1(Q) minus {infinity})`.  Let `e_z` denote its standard basis and
define the signed involution

```text
J e_0=-e_0,                 J e_z=e_(-1/z)  (z!=0).   (NMP1)
```

The minus sign is the hard sign of the polar completion of the deleted
Fourier pair.  The two old cubic carriers have common source `e_0` and
exits `e_(-1),e_(-1/2)`.  Indeed these are the projective images of
`(XT)^2q` and `(XT^2R)^2q`.  Formula `(DFC3)` says that their old carrier
angles tend to `pi/2`; nearest cube-root rounding therefore converges on
the two planes to

```text
C_1 e_0=-(1/2)e_0+(sqrt(3)/2)e_(-1),
C_1 e_(-1)=-(sqrt(3)/2)e_0-(1/2)e_(-1),

C_2 e_0=-(1/2)e_0+(sqrt(3)/2)e_(-1/2),
C_2 e_(-1/2)=-(sqrt(3)/2)e_0-(1/2)e_(-1/2).           (NMP2)
```

Off those planes the rounded cubics equal their old values.  Thus, with
the projective actions `t(z)=z+1` and `r(z)=4z`, they are

```text
C_1 e_z=J e_(z+1)       outside {0,-1},
C_2 e_z=J e_(4z+2)      outside {0,-1/2}.             (NMP3)
```

Set, exactly as in the symmetric retraction,

```text
T_infty=J C_1,             R_infty=T_infty^(-2) J C_2.
```

The fixed words `(J R_infty)^2` and
`R_infty T_infty R_infty^(-1)T_infty^(-4)` are the identity off the ten
coordinates

```text
-2,-1,-1/2,-1/4,0,1/2,1,2,3,4.                       (NMP4)
```

Direct multiplication of the `10 by 10` matrices from `(NMP1)--(NMP3)`
gives

```text
rank(u_infty-1)=rank(v_infty-1)=4,

det(z-u_infty)|_(nontrivial carrier)
 =z^4-(177/64)z^3+(247/64)z^2-(177/64)z+1,

det(z-v_infty)|_(nontrivial carrier)
 =z^4-(315/128)z^3+(437/128)z^2-(315/128)z+1.         (NMP5)
```

For audit, `(NMP5)` uses only the entries `0, plus or minus 1,
plus or minus 1/2, plus or minus sqrt(3)/2` in `(NMP1)--(NMP3)`; the
`sqrt(3)` terms cancel from both characteristic polynomials.  In
particular

```text
Re Tr(u_infty-1)=-79/64,
Re Tr(v_infty-1)=-197/128.                            (NMP6)
```

The relevant finite collection of coherent vectors has Gram matrix
`I+O(a)`.  Gram orthonormalization, the explicit carrier formula, and the
principal-angle formula `1/(sqrt(p)+2)` show that the finite matrices of
`u_p,v_p` on their defect ranges converge in operator norm to the matrices
above.  Outside those ranges the words are exactly the identity; the same
finite expansion also gives the sharper ranks in `(NMC1)`.  Finally, for a
unitary `W`, `||W-1||_F^2=-2 Re Tr(W-1)`.  Applying this to `(NMP6)` proves
`(NMC2)--(NMC4)`.
