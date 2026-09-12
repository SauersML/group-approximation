---
rg: 2
id: leavitt-one-compressor-defect-lies-in-amenable-subgroups
kind: claim
title: The manuscript defect lies in two amenable one-compressor subgroups, the full degree-zero core and the unipotent parabolic
artifacts:
  - research/leavitt-one-compressor-defect-amenable-subgroups-proof.md
  - non_mf_groups_exist.tex
  - GroupApproximation/Manuscript/OneSidedMFRadical/RankTwelveConfiguration.lean
distinct_from:
  leavitt-diagonal-compression-is-elementary-amenable: that fences the diagonal Boolean cylinder algebra `EL_3(D)` with one compressor and locates only the mark `x_13(q)`; this fences the FULL degree-zero core `EL_3(R_0)`, every balanced prefix matrix unit included, and separately the whole unipotent parabolic of every gauge degree, and it locates the manuscript's centralizer `c`, the compressed centralizer `tau c tau^-1`, the test root `l`, and the literal defect commutator `d=[tau c tau^-1,l]` inside the amenable subgroups, so the escape "a non-diagonal root occurrence" is closed unless the occurrence has nonzero degree AND meets an opposite root.
  norm-corona-locally-finite-compression-countermodel: that builds an abstract amenable compression inside a tensor norm corona; this exhibits the phenomenon on the manuscript's own rank-twelve group with the manuscript's own compressor, centralizer, and defect, and says which literal subgroups of the Leavitt group are amenable.
  degree-zero-leavitt-core-has-locally-finite-marked-models: that gives exact finite models of the degree-zero core with constant Weyl words but without the compressor; this adjoins the manuscript compressor and centralizer to the core and proves the resulting infinite subgroup amenable and MF, with the defect surviving.
  finite-positive-root-fragments-have-marked-regular-models: that proves local finiteness of finite positive-root fragments and gives regular models; this uses that local finiteness as one input and adds the compressor, the degree-zero torus, and the centralizer, obtaining an amenable subgroup rather than a finite one.
  compression-defect-dies-in-finite-dimensions: that kills the defect in every finite-dimensional representation of any group; this shows the defect SURVIVES in norm-corona representations of two explicit amenable subgroups of the Leavitt group, so finite-dimensional sterility of the defect is not a T-free MF obstruction on those subgroups.
---

**ESTABLISHED AMENABLE ONE-COMPRESSOR FENCE.**  Keep the manuscript's data:
`R=L_(F_2)(1,2)`, `p=s_0t_0`, `q=s_1t_1`, `H=EL_12(R)`, `L=EL_3(R)` in
positions `0,1,2`, the compressor `tau=diag(X,Y) in H` implementing

```text
tau x_ij(a) tau^-1 = x_ij(s_0 a t_0)          (i,j in {0,1,2}),        (AOC1)
```

the centralizer element `c=x_34(1)`, the test root `l=x_12(1)`, and the
defect

```text
d=[tau c tau^-1, l]=x_02(q) != 1.                                      (AOC2)
```

Let `R_0=union_k B_k`, `B_k=span{s_ut_v:|u|=|v|=k}~=M_(2^k)(F_2)`, be the
full gauge-degree-zero core, and put

```text
L_0=EL_3(R_0)=union_k SL_(3*2^k)(F_2),                                 (AOC3)
P  =U_3(R) semidirect T_0,     T_0=(R_0^x)^3 cap EL_3(R),               (AOC4)
```

the upper unitriangular group of `L` over the WHOLE ring `R` (every root of
every gauge degree) extended by the elementary degree-zero diagonal torus,
which contains `diag(u,u^-1,1)` for every `u in R_0^x` by the Whitehead
lemma.  Both `L_0` and `P` are locally finite.  Then, for `B in {L_0, P}`:

1. `Psi(B) <= B`, where `Psi(A)=qI_3+s_0At_0` is conjugation by `tau`;
2. `tau c tau^-1 = c * x_01(q)`, with `x_01(q) in L_0 cap U_3(R)`, and
   `x_01(q)` centralizes `Psi(B)`;
3. hence `phi(g c^e)=Psi(g) x_01(q)^e c^e` is an injective endomorphism of
   the locally finite group `B x <c>`, and

```text
Lambda_B := <B, tau, c> <= H                                            (AOC5)
```

   is a homomorphic image of the ascending HNN extension `(B x Z/2)*_phi`,
   which is (locally finite)-by-`Z`;
4. `Lambda_B` is elementary amenable, hence operator MF with trivial MF
   radical;
5. `c`, `tau c tau^-1`, `l` and `d` all lie in `Lambda_B`, and `d!=1`, so

```text
d notin Rad_MF(Lambda_(L_0)),        d notin Rad_MF(Lambda_P):           (AOC6)
```

   some norm-matrix-corona homomorphism of each subgroup separates the
   manuscript defect from the identity.

## What this fences

The one-sided compression criterion `thm:compression-criterion` is false
with `L` replaced by `L_0` or by `P`, using the manuscript's own `tau`, `c`,
`l`: every hypothesis except Property `(T)` of `L` is satisfied inside an
amenable group in which the conclusion fails.  Consequently:

* No Property-`(T)`-free derivation of `d in Rad_MF(H)` can use only
  relations that hold in `Lambda_(L_0)`: degree-zero coefficients of ANY
  shape (diagonal cylinders, the cross units `s_0t_1`, `s_1t_0`, whole
  finite matrix rings `B_k`), at any root positions including opposite
  ones, with constant Weyl words, one compressor, and the centralizer.
* No such derivation can use only relations that hold in `Lambda_P`:
  positive-root Heisenberg and additive tables with coefficients of
  arbitrary gauge degree (`s_0`, `t_0`, `s_(00)t_0`, ...), degree-zero
  diagonal units, one compressor, and the centralizer.
* Therefore every load-bearing relation must contain a root coefficient of
  NONZERO gauge degree sitting in an opposite-root (Weyl-mixed)
  configuration, or must involve the complementary compressor `tau'`, or
  some other element outside both subgroups.

The two fences cannot be merged: `SL_3(F_2) <= L_0` contains the Weyl
elements that conjugate `x_01(a)` to `x_10(a)`, so `<L_0,P>=L`, which is
the Property-`(T)` group.  The amenable region is thus exactly the region
where the manuscript's argument has no Property-`(T)` input, and the
Property-`(T)`-free replacement is not a reproof of the same mechanism but
a different theorem consuming mixed-sign nonzero-degree relations.

No Property `(T)`, stability theorem, or trace input is used; the only
literature-level input is `amenable-implies-operator-mf`.

DERIVATION
leavitt-one-compressor-defect-amenable-subgroups-proof
