---
rg: 2
id: derive-choi-input-marginals-and-share-one-hard-edge
kind: route
title: Dualize rank-one corrections and place the hard two-outcome witness on the common tree edge
target: cross-face-choi-annihilation-is-scalar-partition
requires:
  - choi-diagonal-annihilation-equalizes-not-softens
  - ideal-block-infeasibility-has-positive-reservoir-witness
---

First fix `a=rho(ell)` with `ell=ell^* in L`.  For each face, the right side of `(CFA3)`
is a linear functional of `f in B_H^*`.  Finite-dimensional biduality gives
a unique `K_H(a) in B_H`.  If `a>=0` and `f>=0`, the rank-one map

```text
b |-> f(b)a                                                   (1)
```

is completely positive.  Positivity of `Omega_H` therefore gives
`f(K_H(a))>=0` for every positive `f`, proving `K_H(a)>=0`.

Now take an arbitrary Hermitian `f in E^*` with `f(1)=0` and form the unit-zero
reservoir correction

```text
v_f(x)=f(x)ell.                                              (2)
```

Equations `(CFA2)` and `(CFA3)` give

```text
0=Omega(rho o v_f)
 =sum_H f|_(B_H)(K_H(a))
 =f(sum_H K_H(a)).                                          (3)
```

Hermitian functionals separate the self-adjoint part of `E`, so their
annihilator subject to `f(1)=0` is exactly `R 1_E`.  Complexification gives
`C 1_E` for arbitrary `ell`.  Therefore `(3)` proves `(CFA4)`.  When `a>=0`, the sum in `(CFA4)` is
positive, hence its scalar `c_a` is nonnegative.  Taking
`a=rho(x^*x)=rho(x)^*rho(x)` proves `(CFA6)`.  Notice that no inequality in
this derivation compares `c_x` with zero: shared edges enter only through the
concrete equality in `E` in `(3)`.

Conversely choose a basis `(a_k)` of `rho(L)` and preimages `(ell_k)` in
`L`.  Every represented correction has the form
`rho o v=sum_k f_k(.)a_k`; if `rho(v(1))=0`, linear independence gives
`f_k(1)=0`.  Applying `(CFA4)` term by term recovers zero total `Omega` value.
This proves the asserted exactness on the represented correction space.

It remains to prove sharpness with every triangle compatibility present.
Use the packet `rho`, the algebraic native element `y`, and the scalar-image
reservoir `L=span_C{y,y^2}` constructed in
`matrix-unit-choi-diagonal-gauge-counterexample-proof`.  Choose a nontrivial
projection

```text
p in C^*(P_2) subset B_12 cap B_23                         (4)
```

and orthonormal vectors `xi,eta in C^d`.  Define the global unital
self-adjoint map `T:E->M_d` by

```text
T(p)=2P_xi-P_eta+(1/2)(I-P_xi-P_eta),       T(1)=I.         (5)
```

Extend linearly on a self-adjoint complement.  Exactly as in the prerequisite,
surjectivity `rho:I->M_d` lets us start from any quotient section and add one
unit-zero ideal-valued map to obtain a single quotient section `t:E->A` with

```text
rho o t=T.                                                  (6)
```

Because `p` lies in the actual overlap, the two tree restrictions in `(6)`
have literally the same value on `p`; all their other overlap and unit values
also agree because `T` is one map on `E`.

Define

```text
Omega_12(alpha)=<alpha(p)xi,xi>+<alpha(1-p)eta,eta>,
Omega_23(beta) =<beta(p)xi,xi> +<beta(1-p)eta,eta>,
Omega_13(gamma)=<gamma(1)xi,xi>.                            (7)
```

Each functional is nonzero and nonnegative on cp maps.  If `v:E->L` is
self-adjoint and `v(1)=0`, then `rho(v(p))=cI` for a real `c` and
`rho(v(1-p))=-cI`.  Thus each tree component in `(7)` annihilates its
restriction of `rho o v` separately, while the closing component vanishes on
the unit.  This proves `(CFA2)` without using cancellation between faces.

The effect inequalities on the `xi` and `eta` lines show, as before, that
no correction from `L` can make `T(p)` an effect, so the full affine slice is
empty.  Moreover each tree component has value four on `T` and at most two
on a ucp map; the closing component has value one on every unital map.  A ucp
map on `span{1,p}` attaining both tree upper bounds extends to `E` by
Arveson's theorem.  Consequently

```text
Omega(T)=9,       sup_(theta in UCP(E,M_d))Omega(theta)=5,  (8)
```

which proves `(CFA8)`.

Finally, for scalar-output maps `b |-> f(b)I`, each functional in `(7)` has
value `f(1)`.  Hence `(CFA3)` gives `K_H(I)=1` for all three faces, proving
`(CFA9)`.  Since `rho(y)=I`, every density vector used in `(7)` has
`y`-energy one.  The exact scalar partition therefore cannot carry the
missing soft-vector estimate.
