---
rg: 2
id: prefix-address-compresses-one-sided-amitsur-oracle
kind: claim
title: Prefix addresses compress every one-sided Amitsur inverse into five bounded generators
distinct_from:
  one-sided-amitsur-oracle-has-bounded-fock-model: that gives a simultaneous bounded model with countably many named inverse generators q_n; this replaces the whole family by compressions of one bounded operator Q and leaves only five variable generators.
  one-sided-amitsur-oracle-has-two-unitary-corner-model: that removes the inverse variables altogether by testing A_n^*A_n in an external half-corner and leaves only two unitary variables; this is the direct address-compression audit for the original one-sided relations and uses nonunitary generators.
  constant-hs-groupification-of-residual-dimension-tape: that asks for finitely many group relators and runtime-independent transport to a fixed marked carrier; this remains a countably related star-algebra oracle whose dimension-matched relator has growing length and mass.
---

ESTABLISHED.  The countably many left inverses in the one-sided
Amitsur oracle can be compressed into one bounded operator without weakening
the finite-matrix obstruction.  In particular there is a recursively
presented unital star algebra on the five generators

```text
x,y,s_0,s_1,Q
```

which has a bounded infinite-dimensional star representation, while in every
evaluation by `d`-by-`d` matrices its `d`th defining relation has normalized
Hilbert--Schmidt residual exactly one.

Retain the words and standard polynomials

```text
u_j=x y^j x,
p_n=s_(2n)(u_1,...,u_(2n)).                              (PAC1)
```

Put `v_n=s_0^n s_1` and impose only the recursively enumerable family

```text
r_n=(v_n^* Q v_n) p_n-1=0,                 n>=1.          (PAC2)
```

No isometry, orthogonality, or Cuntz relation on `s_0,s_1` is part of this
presentation.

To construct one exact bounded model, let `K` be full Fock space on the
binary alphabet, with left creation isometries `S_0,S_1`, and let `H_0` be
the Fock model from `one-sided-amitsur-oracle-has-bounded-fock-model`.  On
`K tensor H_0` take

```text
x=I tensor L_x,                 y=I tensor L_y,
s_i=S_i tensor I,
V_n=S_0^n S_1 tensor I.
```

The binary words `0^n1` form a prefix-free code, so

```text
V_n^*V_m=delta_(n,m) I.                                      (PAC3)
```

If

```text
q_n=((2n)!)^(-1) p_n(L_x,L_y)^*,
```

then `q_n p_n=I` and `||q_n||=1/sqrt((2n)!)`.  Consequently the
strongly convergent block-diagonal sum

```text
Q=sum_(n>=1) V_n (I tensor q_n) V_n^*                    (PAC4)
```

is bounded, with `||Q||=sup_n ||q_n||=1/sqrt(2)`, and

```text
V_n^* Q V_n=I tensor q_n.                                  (PAC5)
```

Equations `(PAC2)` therefore hold simultaneously in this model.

For the soundness statement, evaluate the five generators by arbitrary
matrices in `M_d(C)`.  Amitsur--Levitzki applies to the `d`-by-`d` matrices
`u_1,...,u_(2d)` and gives `p_d=0`, independently of the values of
`s_0,s_1,Q`.  Hence

```text
r_d=-I_d,                    ||r_d||_(2,d)=1.              (PAC6)
```

Thus address compression removes the infinite generator list without hiding
the moving unit defect.

The construction is not a finite presentation and not a groupification.
The selected relation still depends on `d`; both the address `s_0^d s_1`
and the alternating polynomial grow with `d`; and ordinary telescoping has no
runtime-independent normalized-HS bound.  In particular, adding the proper
isometry relations used in the completeness witness would be invalid: two
isometries with orthogonal ranges already have no nonzero finite-dimensional
model.  The Fock/Cuntz geometry proves existence of one bounded infinite
model only and contributes no finite-matrix relations beyond `(PAC2)`.

