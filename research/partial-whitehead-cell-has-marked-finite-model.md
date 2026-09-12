---
rg: 2
id: partial-whitehead-cell-has-marked-finite-model
kind: claim
title: The first non-scalar Whitehead cell still has a marked finite model
distinct_from:
  scalar-active-mixed-shell-has-marked-regular-model: that permits only coefficients in the scalar active corner; this includes the genuinely non-scalar prefix partial-equivalence symbols and their complete local occurrence table.
  literal-prefix-three-root-swap-retains-typed-carriers: that uses different finite source and target coefficient objects; this gives a same-object finite-field specialization of the whole local signed Whitehead table.
  leavitt-range-sum-fold-does-not-pay-reynolds: that adds the three-path range-sum fold on independent nilpotent factors; this shows why the first partial-equivalence cell remains harmless before the two binary branches are coupled.
  full-signed-whitehead-amalgam-has-fd-invisible-clifford-mark: that includes the full affine-Leavitt coefficient presentation and kills the packet mark in every exact finite-dimensional representation; this isolates the strictly smaller local Whitehead table which still has faithful finite marked quotients.
---

**ESTABLISHED LOCAL COUNTERMODEL.**  Let `k` be the fixed finite splitting
field of odd characteristic and let `B_pe` be the unital `k`-algebra generated
by `e,f,x,y` with the complete signed-prefix occurrence table

```text
yx=e,        xy=f,
fx=x=xe,     ey=y=yf,
(1-f)x=x(1-e)=0,       y(1-f)=(1-e)y=0.               (PWM1)
```

The assignment

```text
epsilon:B_pe -> k,       e,f,x,y |-> 1                 (PWM2)
```

is a unital algebra homomorphism.  Thus every finite Steinberg/root fragment
whose coefficient identities are consequences of `(PWM1)` has an exact
finite model obtained by applying `epsilon` and evaluating its roots in
`EL_n(k)`.

This model retains the active mark.  The unit of `B_pe` is the active
idempotent `A`, so

```text
epsilon(x_ij(A))=x_ij(1)!=1.                            (PWM3)
```

Moreover the signed prefix Whitehead word

```text
W=x_12(x)x_21(-y)x_12(x)                               (PWM4)
```

maps to the standard rank-one Weyl matrix

```text
w=[[0,1],[-1,0]],             w^2=-I,       w^4=I.     (PWM5)
```

Consequently the scalar active shell, every positive and negative root
occurrence needed to authenticate `(PWM1)`, the literal reuse of the first
and third factors in `(PWM4)`, and the relation `W^4=1` all coexist in one
finite exact model while the active root survives.  The left regular
representation of the finite image has zero relator defect and keeps the
marked root at normalized-HS distance `sqrt(2)`.

The local controlled-packet graft also has finite marked models.  Let `D` be
the finite controlled-Pauli packet in
`full-signed-whitehead-amalgam-has-fd-invisible-clifford-mark`, with its
order-four element `u` and nontrivial central packet mark `J`.  Form

```text
Gamma_loc=D *_(<u>=<w>~=C_4) EL_n(k).                  (PWM6)
```

This is a finite graph of finite groups, hence virtually free and residually
finite.  Bass--Serre normal form embeds both vertex groups.  A finite quotient
can therefore be chosen injective on both finite vertex groups simultaneously.
Its regular representation restricts to multiples of both vertex regular
representations, so both `J` and `x_ij(1)` survive with their canonical finite
packet traces and every local Whitehead/controlled-packet row is exact.

This strictly narrows the first possible non-scalar payment.  The partial
equivalence `x,y` and all its support/product occurrences do not suffice.
A load-bearing fragment must destroy the marked finite specialization
`(PWM2)`.  In the native Leavitt language that requires coupling the cell to
the second branch and its crossed-zero/range-sum data, or an equivalent
relation which distinguishes the proper fine corner `f` from the coarse
corner `e`.  Even scalar equality of the resulting range-sum fold is not
enough by `leavitt-range-sum-fold-does-not-pay-reynolds`; the collapse-killing
coefficient occurrences must also be coupled to the packet payload whose
Reynolds leakage is measured.

The theorem does not construct a finite model of the full affine-Leavitt
presentation.  Such a model with surviving active mark is excluded by
`affine-leavitt-steinberg-mark-is-fd-invisible`.  Its point is the exact
minimality boundary: the first non-scalar Whitehead row lies strictly below
that full coefficient obstruction.

DERIVATION
partial-whitehead-finite-model-proof
