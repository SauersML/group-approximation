---
rg: 2
id: two-depth-one-leavitt-roots-return-only-constantly
kind: claim
title: Two depth-one Leavitt roots return to the signed Hecke pair only by constant same-root collapse
artifacts:
  - experiments/depth_one_paired_leavitt_return_search.py
  - research/depth-one-paired-leavitt-return-enumeration.md
distinct_from:
  one-asymmetric-prefix-cannot-be-signed-hecke-return: that treats one nonconstant insertion in each of the eight external constant-return positions; this exhausts two nonconstant factors over all forty-two ordered root positions.
  full-depth-one-leavitt-menu-has-finite-clifford-model: that gives a finite gauge model for the named depth-one ESB actor menu; this classifies every ordered pair of depth-one Leavitt matrix-unit roots, including positions and products absent from that menu, directly against the full signed Hecke normalizer condition.
  paired-critical-opposite-roots-return-only-trivially: that treats an arbitrary coefficient pair in one critical opposite-root channel by a two-by-two block calculation; this simultaneously permits all root-channel pairs but restricts each coefficient to the eight depth-one matrix units.
  asymmetric-depth-two-fold-return-retains-external-gauge: that constructs a three-leaf depth-two same-root return; this proves why neither a two-letter depth-one precursor nor a mixed depth-one root-channel pair can supply it.
---

**ESTABLISHED ALL-POSITION TWO-LETTER FENCE.**  Let

```text
M_1={s_mu t_nu: mu,nu in {empty,0,1}} minus {1},      (DPR1)
```

so `M_1` consists of the eight nonconstant coefficients

```text
s_0,s_1,t_0,t_1,s_0t_0,s_0t_1,s_1t_0,s_1t_1.
```

For all `42` ordered root positions on the actor coordinates
`{2,4,5,6,7,8,9}`, consider products

```text
g=x_ab(r)x_cd(s),                    r,s in M_1,       (DPR2)
```

under the hypothesis that both factors individually fail to normalize the
signed pair `(L_0,lambda_0)`.  There are `336` individual nonconstant roots.
Exactly `32` already normalize the pair: all eight coefficients in each of
the four positions

```text
x_26(*), x_76(*), x_29(*), x_79(*).                   (DPR3)
```

Thus `(DPR2)` has exactly `304^2=92416` ordered cases.

Among them, exactly `338` products normalize `(L_0,lambda_0)`, and every one
is a constant same-root collapse.  They are precisely:

```text
x_ab(r)x_ab(r)=1                                      (304 cases),
x_ab(s_0t_0)x_ab(s_1t_1)=x_ab(1),
x_ab(s_1t_1)x_ab(s_0t_0)=x_ab(1)                     (34 cases), (DPR4)
```

where the last two rows occur at the `17` constant signed-normalizer root
positions not excluded by `(DPR3)`.  After removing identities and constant
products, the number of genuinely paired nonconstant returns is zero:

```text
x_ab(r),x_cd(s) notin Norm(L_0,lambda_0),
x_ab(r)x_cd(s) in Norm(L_0,lambda_0)
 ==> (a,b)=(c,d) and the product is constant.          (DPR5)
```

The test is exact in the binary Leavitt algebra, not a finite-boundary
approximation.  A monomial `s_mu t_nu` is stored as the prefix replacement
`nu gamma -> mu gamma`, with the exact common-domain expansion

```text
(mu,nu)=(mu0,nu0)+(mu1,nu1).                           (DPR6)
```

Prefix cancellation multiplies these normal forms.  For every candidate,
the ten signed `L_0` generators are conjugated symbolically; each resulting
entry is tested for equality with `0` or `1` by `(DPR6)`, and the resulting
constant matrix is checked in the exact `8192`-element character ledger of
`L_0`.  The identities in `(DPR4)` are then rechecked directly from
characteristic two and `s_0t_0+s_1t_1=1`.

Therefore a depth-one two-letter word cannot even meet the full-Gram return
condition `(ESB1)`, so no Singer mixed relation arises at this scope.  The
next coefficient-sensitive candidate must use at least three prefix leaves,
depth-two address data, or more than two nonconstant root occurrences.  No
Property `(T)`, Kazhdan input, trace profile, literature result, local
computation, or local build is used.

DERIVATION
depth-one-paired-leavitt-return-enumeration
