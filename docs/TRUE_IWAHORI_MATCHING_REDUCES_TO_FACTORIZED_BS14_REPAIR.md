# Iwahori matching reduces to factorized `BS(1,4)` repair

Date: 2026-08-14

## 1. Outcome

After matching the central sign, the two noncentral Iwahori relations can be
compressed into one Baumslag--Solitar relation.

Let

```text
alpha,beta:K=SL_2(Z)->U(d)                            (FBS1)
```

be exact representations.  Put

```text
A=alpha(w),          B=beta(w),
X=beta(u),           Y=alpha(l),
C=AB,                                                  (FBS2)
```

where `wuw^(-1)=l^(-1)`.  If the Iwahori defect is at most `delta`, then

```text
||C X C^*-X^4||_2<=3delta.                            (FBS3)
```

Conversely, suppose the two modular vertex representations are exact, their
central signs agree, the upper Iwahori relation is exact,

```text
alpha(u)=X^2,                                         (FBS4)
```

and

```text
C X C^*=X^4.                                          (FBS5)
```

Then the lower Iwahori relation is automatic:

```text
alpha(l)^2=beta(l).                                   (FBS6)
```

Thus the Dogon--Vigdorovich matching problem reduces to a structured
simultaneous repair problem for three individually Hilbert--Schmidt stable
relation sets (the first is initially only approximate because
`X^2` is only close to `alpha(u)`):

```text
(A,X^2) is a modular representation,
(B,X)   is a modular representation,
(AB,X)  is a BS(1,4) representation,                 (FBS7)
```

with `A^2=B^2` carrying the common central sign.

The group `BS(1,4)` is Hilbert--Schmidt stable.  Therefore the fourth-power
dynamical relation by itself is repairable.  The precise remaining gate is
**factorized `BS(1,4)` repair**: perform that correction while keeping the
stable letter factored as `A'B'`, where `(A',(X')^2)` and `(B',X')` remain
exact modular representations with the same central square.

This is a stronger reduction than separate spectral flag repair.  It uses
the actual product of the two modular Weyl unitaries, not an arbitrary
eigenvalue permutation, and it shows that exact repair of the product
dynamics plus the two vertex relations automatically repairs both Iwahori
edges.

## 2. The two exact modular conjugacies

Let

```text
u=[[1,1],[0,1]],       l=[[1,0],[1,1]],
w=[[0,-1],[1,0]].                                      (FBS8)
```

One has

```text
w u w^(-1)=l^(-1),             w^2=-1.                (FBS9)
```

Since conjugation by `w` has order two, `(FBS9)` gives in the two exact
vertex representations

```text
A Y^(-1) A^*=alpha(u),
B X^(-1) B^*=beta(l).                                 (FBS10)
```

After inversion, the second identity is

```text
B X B^*=beta(l)^(-1).                                 (FBS11)
```

The noncentral Iwahori defect is

```text
||alpha(u)-X^2||_2<=delta,
||beta(l)-Y^2||_2<=delta.                             (FBS12)
```

## 3. Proof of the approximate fourth-power relation

From the second line of `(FBS12)` and unitary invariance,

```text
||B X B^*-Y^(-2)||_2
 =||beta(l)^(-1)-Y^(-2)||_2
 <=delta.                                              (FBS13)
```

Conjugate by `A` and use the first identity in `(FBS10)`:

```text
||A B X B^* A^* - alpha(u)^2||_2<=delta.              (FBS14)
```

For unitaries, squaring is `2`-Lipschitz in normalized
Hilbert--Schmidt norm.  The first line of `(FBS12)` therefore gives

```text
||alpha(u)^2-X^4||_2<=2delta.                         (FBS15)
```

The triangle inequality in `(FBS14)--(FBS15)` proves `(FBS3)`.

Thus `(C,X)` is a `3delta`-solution of the defining relation

```text
c x c^(-1)=x^4                                       (FBS16)
```

of `BS(1,4)`.

## 4. Proof of the converse

Assume `(FBS4)--(FBS5)`.  The first identity in `(FBS10)` and `(FBS4)` give

```text
A Y^(-1) A^*=X^2.                                    (FBS17)
```

Squaring,

```text
A Y^(-2) A^*=X^4.                                    (FBS18)
```

On the other hand, `(FBS5)` says

```text
A B X B^* A^*=X^4.                                   (FBS19)
```

Cancel `A` from `(FBS18)--(FBS19)`:

```text
B X B^*=Y^(-2).                                      (FBS20)
```

Invert `(FBS20)` and use the second identity in `(FBS10)`:

```text
beta(l)=B X^(-1)B^*=Y^2=alpha(l)^2.                  (FBS21)
```

This is `(FBS6)`.

The common central relation must still be imposed.  The upper and lower
unipotent identities alone do not force it, as already noted in
`TRUE_IWAHORI_MATCHING_FIXED_TYPE_REDUCTION.md`.  After the central-sign
matching lemma in that note, it is simply

```text
A^2=B^2=chi(-1)1.                                    (FBS22)
```

Equations `(FBS4)`, `(FBS6)`, and `(FBS22)` are exactly the three edge
generator identities, so the two vertex representations glue.

## 5. The dynamical subgroup is already stable

The group

```text
BS(1,4)=<c,x | cxc^(-1)=x^4>                         (FBS23)
```

is the metabelian group

```text
Z[1/4] semidirect Z.                                  (FBS24)
```

Levit--Vigdorovich prove Hilbert--Schmidt stability of `BS(1,n)` for every
integer `n`, using the density of periodic measures for multiplication by
`n` on the corresponding solenoid.  Therefore any sequence `(C_n,X_n)`
satisfying `(FBS3)` with `delta_n->0` is Hilbert--Schmidt close to exact
pairs

```text
C'_n X'_n (C'_n)^*=(X'_n)^4.                         (FBS25)
```

This theorem repairs the actual dynamical conjugator `C=AB`; unlike a
Hoffman--Wielandt eigenvalue matching, it does not replace `C` by an
unrelated spectral permutation.

Reference:

- A. Levit and I. Vigdorovich, *Characters of solvable groups,
  Hilbert--Schmidt stability and dense periodic measures*,
  [arXiv:2206.02268](https://arxiv.org/abs/2206.02268), in particular the
  `BS(1,n)` application of their character/dense-periodic-measure criterion.

## 6. Why separate stability does not yet finish

Apply `BS(1,4)` stability to obtain `(C',X')` as in `(FBS25)`.  Since
`C'` is close to `AB`, one can certainly factor it near `A,B` algebraically;
for example,

```text
C'=A(A^*C'),                  A^*C' approximately B.  (FBS26)
```

But the second factor in `(FBS26)` need not be the Weyl image of a modular
representation with unipotent image `X'`.  Likewise, independently
correcting the two approximate modular pairs by Hilbert--Schmidt stability
of `SL_2(Z)` need not preserve their product as the corrected `BS(1,4)`
stable letter.

The exact remaining theorem is:

> **Factorized `BS(1,4)` repair.**  Suppose `(A_n,(X_n)^2)` and
> `(B_n,X_n)` are asymptotically modular pairs with exact matched central
> squares, while `(A_nB_n,X_n)` has vanishing `BS(1,4)` defect.  Then there
> are nearby exact modular pairs `(A'_n,(X'_n)^2)` and `(B'_n,X'_n)` such
> that `(A'_nB'_n,X'_n)` satisfies the `BS(1,4)` relation exactly.

By Section 4, this theorem gives exact Iwahori compatibility.  By the
Dogon--Vigdorovich criterion, it then gives an explicit nonhyperlinear
finite central extension of `SL_2(Z[1/2])`.

The three relation sets in `(FBS7)` are each individually
Hilbert--Schmidt stable:

1. `SL_2(Z)` is virtually free;
2. the second copy of `SL_2(Z)` is virtually free; and
3. `BS(1,4)` is stable by Levit--Vigdorovich.

What remains is stability of their shared-variable factorization, not
stability of any one constituent group.  This identifies the final
nonlinear synchronization datum in a three-unitary package `(A,B,X)`.

For the first two items, see M. Gerasimova and K. Shchepin,
*Virtually free groups are p-Schatten stable*,
[arXiv:2107.10032](https://arxiv.org/abs/2107.10032).  They prove normalized
`p`-Schatten stability for every finitely generated virtually free group,
and hence Hilbert--Schmidt stability at `p=2`.
