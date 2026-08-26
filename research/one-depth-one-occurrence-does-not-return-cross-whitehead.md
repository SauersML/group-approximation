---
rg: 2
id: one-depth-one-occurrence-does-not-return-cross-whitehead
kind: claim
title: One depth-one occurrence does not return an individual cross Whitehead to either native Hecke target
artifacts:
  - experiments/individual_cross_whitehead_one_return_search.py
  - research/one-depth-one-cross-whitehead-return-enumeration.md
distinct_from:
  individual-cross-whiteheads-miss-native-hecke-target: that proves `K_i` alone misses both targets and leaves one additional coefficient-sensitive return open; this exhausts one elementary or one opposite-root Whitehead occurrence over the full depth-one coefficient menu.
  two-depth-one-leavitt-roots-return-only-constantly: that searches products of two arbitrary elementary exits for returns to the source signed normalizer; this fixes the nonlinear three-root word `K_i`, permits a three-factor Whitehead as the additional occurrence, and also tests the native `J_1` target.
  one-asymmetric-prefix-cannot-be-signed-hecke-return: that inserts one nonconstant arm into one of eight constant external normalizers; this starts from the nonconstant cross-branch Whitehead and tests every actor root position against the full signed subgroup.
---

**ESTABLISHED BOUNDED RETURN FENCE.**  Keep

```text
p=s_0t_1,                 r=s_1t_0,
K_0=x_78(p)x_87(r)x_78(p),
K_1=x_78(r)x_87(p)x_78(r),                            (DOR1)
```

and the signed Hecke pair `(L_0,lambda_0)` on actor coordinates
`(2,4,5,6,7,8,9)`.  Let `Q=e_(L_0,lambda_0)` and retain the literal native
Whitehead `J_1`.

Use the complete nonconstant depth-one prefix menu

```text
D_1={s_mu t_nu: mu,nu in {empty,0,1},
                   (mu,nu)!=(empty,empty)}.           (DOR2)
```

Thus `|D_1|=8`.  The additional occurrence `L` is allowed to be either

```text
x_ab(c),
or x_ab(c)x_ba(d)x_ab(c),                             (DOR3)
```

where `a!=b` are any of the `42` oriented actor-coordinate pairs and
`c,d in D_1`.  This is all `336` depth-one elementary occurrences and all
`2688` depth-one three-factor opposite-root Whitehead occurrences.

For each `i=0,1`, exact prefix-normal-form enumeration gives

```text
LK_i in Norm(L_0,lambda_0)                            (DOR4)
```

only for the following two spellings:

```text
i=0: L=x_78(p)x_87(r)x_78(p)
       or x_87(r)x_78(p)x_87(r),

i=1: L=x_78(r)x_87(p)x_78(r)
       or x_87(p)x_78(r)x_87(p).                      (DOR5)
```

The two spellings in each row are the same partial Whitehead matrix:

```text
L=K_i,                     LK_i=1.                    (DOR6)
```

Hence all four hits are the tautological cancellation, not an additional
return occurrence.  There are no elementary-root hits and no genuine
Whitehead hits.

For the native row-one target, the exact condition is

```text
J_1^(-1)LK_i in Norm(L_0,lambda_0).                   (DOR7)
```

There are **zero** solutions to `(DOR7)` in the entire menu `(DOR2)--(DOR3)`.
Every candidate was tested simultaneously on all ten signed generators of
`L_0`; membership and the `lambda_0` sign were checked after every
conjugation.  In total the audit performs

```text
2 branches * 2 targets * 3024 candidates = 12096      (DOR8)
```

full signed-signature tests, under a hard cap of `20000`.

The row-vector obstruction explains the first layer of the result.  With
`h=x_28(1)`, the two exposed rows on columns `(7,8)` are

```text
K_0hK_0: (r,q_0),          K_1hK_1: (p,q_1).          (DOR9)
```

One elementary shear leaves one of these two nonconstant components
untouched, while an off-block root creates an additional exposed component.
The full ten-generator audit handles the remaining incidences and the
three-factor candidates.

This is a sharply scoped finite-menu no-go.  It does not rule out a
depth-two coefficient, a product of two additional nonnormal occurrences,
or a longer asymmetric Whitehead.  Any next search must cross one of those
boundaries; repeating one depth-one opposite cell cannot return `K_i` to
either native target.

No Property T, Kazhdan input, trace hypothesis, local computation,
literature theorem, or Lean compilation is used.

DERIVATION
one-depth-one-cross-whitehead-return-enumeration
