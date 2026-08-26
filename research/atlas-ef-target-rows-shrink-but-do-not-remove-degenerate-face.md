---
rg: 2
id: atlas-ef-target-rows-shrink-but-do-not-remove-degenerate-face
kind: claim
title: The first moving-coefficient Atlas rows mix the 1-7-7 strata but retain a 15/4096 face
distinct_from:
  atlas-target-gl3-preserves-the-fifteen-type-degeneracy: that exhausts coefficient-one target basis changes, which preserve the three degenerate strata; this uses the first nontrivial coefficients e,f and computes the resulting affine translations between the strata.
  orthogonal-steinberg-root-spectral-support-is-not-additive: that gives a static support counterexample for two orthogonal idempotents; this computes how the Leavitt equations pe=e, qe=0, pf=0, qf=f control the moving-target root characters.
  atlas-pauli-branch-recurrence-automaton: that asks for a complete recurrent low-energy network; this identifies one exact finite moving-coefficient subsystem and its still-positive fixed face.
---

**ESTABLISHED EXACT MIXING AND SMALLER SURVIVOR.**  Let `p=eE`, `q=fF`.
For distinct `r,s in {3,4,5}`, the shortest target-mixing rows with a
nontrivial coefficient use

```text
A_rs=x_rs(e),       B_rs=x_rs(f),
D_(r,a)=x_1r(a).                                      (EFR1)
```

The Steinberg relation and the four elementary Leavitt products

```text
pe=e,       qe=0,       pf=0,       qf=f              (EFR2)
```

give

```text
A_rs D_(r,p) A_rs = D_(r,p) D_(s,e),
A_rs D_(r,q) A_rs = D_(r,q),
B_rs D_(r,p) B_rs = D_(r,p),
B_rs D_(r,q) B_rs = D_(r,q) D_(s,f).                 (EFR3)
```

On a joint target-character sector put

```text
alpha=1 iff D_(s,e) has sign -1,
beta =1 iff D_(s,f) has sign -1.                      (EFR4)
```

In the `(u,w)` coordinates of the three-shear classification, with `e_r`
the `r`th coordinate vector, `(EFR3)` is the exact affine action

```text
A_rs : (u,w) |-> (u+alpha e_r, w+alpha e_r),
B_rs : (u,w) |-> (u,             w+beta e_r).         (EFR5)
```

Thus moving coefficients genuinely cross the old strata:

* an active `e` row joins the singleton type `A` to type `C` and can send a
  type-`B` character into the balanced region;
* an active `f` row joins `A` to `B` and can send a type-`C` character into
  the balanced region;
* if `alpha=beta=1`, the four-point affine orbit of `(EFR5)` meets the
  balanced region from every one of `A,B,C`.  Combining with the three
  source shears then pairs the marked `p/q` orientations.

Nevertheless this family still has an exact fixed face.  If all six target
signs

```text
D_(r,e)=D_(r,f)=+1,       r=3,4,5,                    (EFR6)
```

are positive, every `e/f` translation in `(EFR5)` is trivial.  Coefficient-
one `GL_3(F_2)` rows only permute these positive signs, so the full
coefficient-one plus `e/f` target packet reduces on `(EFR6)` to the preceding
three-shear packet.  Its six marked orientation orbits on the `1,7,7`
degenerate strata survive unchanged.

The survivor has exact canonical mass.  At the three target root positions,
the twelve coefficient roots for

```text
p,q,e,f
```

form `C_2^12`: the four coefficients are linearly independent in the
additive Leavitt algebra, and the three matrix positions are independent.
Consequently the `e/f` fixed face `(EFR6)` has trace `1/64`, independently
of the `p/q` character.  Intersecting it with the old `15/64` degeneracy face
gives

```text
tr(target survivor)=15/4096.                           (EFR7)
```

After also imposing the marked source sign `x_12(1)=-1`, its ambient
canonical trace is

```text
15/8192.                                                (EFR8)
```

This is small but dimension-independent.  Permutation representations of
one surviving marked orientation orbit give exact finite-dimensional local
countermodels; the other orientation need not be present.

Therefore the first nontrivial moving coefficients do not eliminate the
Atlas positive face.  They shrink it from `15/64` to an explicitly positive
`15/4096` target mass.  The next unused rows are those with coefficients
`E,F` (which leave the finite `{p,q,e,f}` window) or another incidence that
returns those new coefficient characters to the CK window.

DERIVATION
atlas-ef-target-row-affine-proof
