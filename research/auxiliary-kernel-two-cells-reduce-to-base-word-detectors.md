---
rg: 2
id: auxiliary-kernel-two-cells-reduce-to-base-word-detectors
kind: claim
title: Every killable-auxiliary two-cell reduces to a literal base-word detector
distinct_from:
  load-bearing-hnn-substitution-is-an-ordinary-packet-detector: that treats one HNN row around a split Steinberg Whitehead word; this gives the presentation-level substitution theorem for arbitrary finite relator menus and applies in particular to non-Bass--Serre marked two-cells.
  split-steinberg-conditional-swap-has-root-kernel-countermodel: that constructs the root-kernel countermodel for the minimal additive Whitehead system; this identifies the common reason that the same countermodel persists for lamp, Clifford, and zero-compression attachments.
  central-marked-two-cycle-zero-compression-cell: that robustly consumes a two-periodic selected projection once its grading is authenticated; this proves that feeding it a selected-representation-only lamp reflection leaves an exact positive-payload kernel model.
---

**ESTABLISHED SUBSTITUTION FENCE.**  Let

```text
K=<X | R_K>
```

be an ordinary base presentation and let `A` be a finite set of auxiliary
generators.  For a finite relator menu `R` in `F(X union A)`, form

```text
Gamma=<X,A | R_K,R>.                                   (AKT1)
```

Let `epsilon:F(X union A)->F(X)` fix `X` and send every element of `A` to
one.  Put

```text
R_0={epsilon(r):r in R},
K_0=<X | R_K,R_0>.                                    (AKT2)
```

Then there is a canonical retraction

```text
Gamma -> K_0,          x |-> x,       a |->1.          (AKT3)
```

Consequently, if a finite-dimensional representation `rho_0` of `K`
satisfies all the residual words `R_0`, then it extends to an **exact**
finite-dimensional representation of `Gamma` by taking every auxiliary
generator equal to the identity.

Apply this to the finite uniform-assignment/role-packet model of the shared
BCS structural group.  This model keeps the central mark nontrivial and has

```text
tau(B_f)>0.                                            (AKT4)
```

If it satisfies `R_0`, its pullback through `(AKT3)` has zero presentation
defect and the same positive forbidden payload.  Every actuator word in
`ker(epsilon)` becomes the identity.  Thus no overlap loss, selected-row
defect, or positive-density payload floor can follow from `(AKT1)`.

This includes the most economical attempted composition of the two positive
front ends already in Cairn.  Let `r_(F,s)` be the `V_4` lamp word from
`one-round-v4-lamps-wordize-a-bcs-losing-projection`, and adjoin an involution
`z` together with the non-Bass--Serre marked two-cycle relations

```text
[r_(F,s),W]=[r_(F,s),z]=1,
W z W^(-1)=r_(F,s)z,                                  (AKT5)
```

where `W` may be any word in the original payload generators.  In the
selected operator realization one has

```text
r_(F,s)=1-2L_(F,s,B),
q=(1-r_(F,s))(1-z)/4,
qWq=0.                                                 (AKT6)
```

But the presentation does not authenticate the first equality.  Sending all
`V_4` lamps and `z` to one makes every relation in `(AKT5)` an identity while
leaving `W` arbitrary.  Hence the finite positive-payload base model extends
exactly, with the selected source in `(AKT6)` replaced by zero.  The robust
zero-compression theorem is correct; the lamp-to-shared-payload identification
is the entire missing statement.

The countermodel survives the natural parity synchronization rows.  Write
`Omega=F_2^k`, use bits `a_j`, and distinguish the marked-cycle grading `c`
from the lamp generators `z_a,b_a`.  The selected realization satisfies

```text
product_a z_a=J,
product_(a:a_j=1) z_a=x_j,                 1<=j<=k,
product_a b_a=B.                                       (AKT7)
```

Assume that both the forbidden set `F` and its complement are nonempty.  For
**every** scalar context assignment

```text
J=-1,       x_j=(-1)^(t_j),       B=(-1)^b,            (AKT8)
```

there are scalar lamp signs satisfying `(AKT7)` and

```text
r_(F,s)=1.                                             (AKT9)
```

Indeed, in additive `F_2` notation the equations on the `z_a` have coefficient
columns

```text
(1,a_1,...,a_k),             a in F_2^k.
```

These span `F_2^(k+1)`: the column at `a=0` gives the first basis vector and
its sum with the columns at the standard basis assignments gives every other
basis vector.  Thus choose the `z_a` with the required total parity and visible
parities.  Their contribution to `r_(F,s)` is now one scalar sign `d`.  Choose
the product of the `b_a` over allowed coordinates to be `d`, making
`r_(F,s)=1`; because there is at least one forbidden coordinate, choose the
product of the remaining `b_a` to make the total product equal to `B`.

Taking `c=1` makes the marked two-cycle relation

```text
W c W^(-1)=r_(F,s)c
```

exact.  Direct-summing these scalar lifts over all assignments produces a
finite diagonal model with positive forbidden mass and zero relator defect.
Thus the obvious group-word synchronizations recover the visible parities but
not the one-hot assignment PVM; they do not authenticate the lamp reflection.

There is also a dimension-free quantitative version of the substitution.
For a relator `r`, let `N_A(r)` count occurrences of auxiliary letters.  For
any unitary tuple,

```text
||rho(epsilon(r))-1||_2
 <=||rho(r)-1||_2
   +N_A(r) max_(a in A)||rho(a)-1||_2.                (AKT10)
```

This is the usual telescoping estimate, including inverse occurrences since
`||rho(a)^(-1)-1||_2=||rho(a)-1||_2`.  Therefore near the auxiliary kernel,
any dimension-uniform floor obtained from the full two-cell already gives,
with fixed constants, a floor for one of the residual literal base words.

## Exact boundary

The theorem does not rule out a relation whose auxiliary-kernel substitution
is a genuinely nontrivial word `g(X)` which vanishes in the perfect trace but
cannot vanish on positive forbidden payload in finite matrices.  It proves
that this `g` is not manufactured by the auxiliary two-cell: it is already a
literal shared-payload detector.  Nor does it cover a completion whose
perfect protected sector necessarily uses a nontrivial auxiliary quotient;
`finite-cyclic-actor-root-kernel-dichotomy` treats that finite-actor variant.

Thus the smallest surviving non-Bass--Serre gate is sharply constrained:

```text
one mixed relation with a nontrivial residual base word,
trivial in the perfect BCS trace,
and carrying a dimension-independent defect on every positive-payload
finite matrix model.                                 (AKT11)
```

Constructing `(AKT11)` is precisely the shared nonlinear BCS-to-group word
detector.  Pure lamp/root/Whitehead/marked-two-cycle syntax whose residual
word is trivial cannot supply it.

DERIVATION
auxiliary-kernel-substitution-proof
