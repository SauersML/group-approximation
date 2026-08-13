# A uniformly local integral packet basis controls harmonic systoles and lifts

Date: 2026-08-11

## Outcome

The level-`121` computation suggests that increasing harmonic rank is not by
itself dangerous.  This note gives a precise structural theorem explaining
one mechanism that would make that observation uniform.

For each finite chart `X`, let `Q_X` be the projected harmonic cycle lattice
and let `Q_X^#` be its Euclidean dual.  Suppose `Q_X` has an integral basis
whose synthesis operator is uniformly bounded.  Then

```text
lambda_1(Q_X^#) >= 1/A.                              (HRP1)
```

If the dual basis also has integral ambient lifts with uniformly bounded
synthesis operator, the resulting integral section has uniformly bounded
norm:

```text
kappa_X <= A K.                                      (HRP2)
```

Both hypotheses follow from bounded Gram row sums.  Thus a basis made from
bounded local packets with bounded overlap proves the desired family theorem
even if the harmonic rank tends to infinity.  The theorem isolates a concrete
arithmetic target for the projective family: construct compatible harmonic
and lift packets, rather than compute an SVP or a closest lift independently
at every level.

This note proves the implication.  It does **not** yet construct such packet
bases for every projective chart.

## 1. Dual systole from one upper Riesz bound

Let `H` be a Euclidean space of dimension `r`, let `Q subset H` be a full
lattice, and choose a `Z`-basis

```text
q_1,...,q_r of Q.                                    (HRP3)
```

Let

```text
T:R^r -> H,       T a=sum_i a_i q_i,                 (HRP4)
G_Q=T^*T=(<q_i,q_j>)_(i,j).                          (HRP5)
```

Write `q_1^*,...,q_r^*` for the dual basis of `Q^#`.

**Theorem 1 (upper-Riesz dual systole bound).**  If

```text
||T|| <= A,                                           (HRP6)
```

then

```text
lambda_1(Q^#) >= 1/A.                                (HRP7)
```

Equivalently, it suffices that

```text
lambda_max(G_Q) <= A^2.                              (HRP8)
```

**Proof.**  Let `0!=u in Q^#` and put

```text
a=T^*u=(<u,q_1>,...,<u,q_r>) in Z^r.                 (HRP9)
```

Because the `q_i` span `H`, `a` is nonzero.  Hence `||a||_2>=1`.  On the
other hand,

```text
||a||_2=||T^*u||<=||T||||u||<=A||u||.                (HRP10)
```

Thus `||u||>=1/A`.  Taking the minimum proves `(HRP7)`.  The equivalence of
`(HRP6)` and `(HRP8)` is the identity `||T||^2=lambda_max(T^*T)`.  End proof.

This uses only an **upper** bound on the primal basis.  No lower Riesz bound,
reduced dual basis, regulator estimate, or fixed rank is required.

## 2. The spherical product

Let `B_X` be the maximum norm of the selected nonzero integral spherical
templates in chart `X`.  If

```text
inf_X B_X >= b>0                                     (HRP11)
```

and every `Q_X` has a basis satisfying `(HRP6)` with the same `A`, then

```text
inf_X B_X lambda_1(Q_X^#) >= b/A>0.                 (HRP12)
```

For the ordinary Euclidean cellular norm, a nonzero integral template has
norm at least one, so one may take `b=1`.  If a normalized or weighted norm
is used, `(HRP11)` must instead be checked in that norm.

The product bound `(HRP12)` rules out denominator collapse.  If in addition
`b/A>=1`, every chart is above the spherical threshold.  A merely positive
constant need not eliminate every subthreshold class, but the lift theorem
below controls all of them at once.

## 3. Compatible integral lift packets

Use the harmonic exact sequence from
`TRUE_HARMONIC_INTEGRAL_LIFT_SEQUENCE.md`:

```text
0 -> L -> M_Sigma --P_Sigma--> Q^# -> 0.             (HRP13)
```

For the basis `(HRP3)`, choose integral elements `z_i in M_Sigma` such that

```text
P_Sigma(z_i)=q_i^*.                                  (HRP14)
```

Let

```text
Z:R^r -> span_R(M_Sigma),   Z a=sum_i a_i z_i,       (HRP15)
G_Z=Z^*Z=(<z_i,z_j>)_(i,j).                          (HRP16)
```

**Theorem 2 (packet-section bound).**  If

```text
||T||<=A,             ||Z||<=K,                      (HRP17)
```

then the rule

```text
s(sum_i a_i q_i^*)=sum_i a_i z_i                    (HRP18)
```

is a `Z`-linear section of `(HRP13)` satisfying

```text
||s||<=A K.                                           (HRP19)
```

Consequently

```text
kappa_Sigma<=A K,                                    (HRP20)
```

for the optimal Euclidean harmonic lift distortion of `(HIL19)`.

**Proof.**  Equation `(HRP14)` makes `(HRP18)` a section.  For
`u=sum_i a_i q_i^*`, duality gives exactly

```text
a=T^*u.                                               (HRP21)
```

Therefore

```text
||s(u)||=||Za||<=K||a||_2
                   =K||T^*u||<=KA||u||.             (HRP22)
```

Taking the operator norm proves `(HRP19)`.  Every section is a candidate
lift for every lattice vector, so `(HRP20)` follows from `(HIL24)`.  End
proof.

Unlike a class-by-class lifting statement, Theorem 2 controls every element
of `Q^#`, including every class satisfying `B_X||u||<1`.

### Exact nonlinear graph norm

The full circle-repair metric uses the Moore--Penrose graph norm.  Put

```text
zhat_i=(q_i^*, A_boundary^dagger(z_i-q_i^*))          (HRP23)
```

in the orthogonal graph space, and let `Zhat` be their synthesis operator.
The same proof, with `Zhat` in place of `Z`, gives

```text
||T||<=A, ||Zhat||<=K_graph
  ==> kappa_(A_boundary,Sigma)<=A K_graph.            (HRP24)
```

Thus the packet criterion applies directly to the exact nonlinear repair
norm; no Euclidean-to-ellipsoidal comparison is necessary.  Alternatively,
the universal real Hodge gap converts a Euclidean lift bound into a graph
bound through `(HIL16d)`.

## 4. A local bounded-overlap criterion

The spectral conditions in Theorems 1 and 2 have a purely local sufficient
form.

**Theorem 3 (Gram row-sum criterion).**  If

```text
max_i sum_j |<q_i,q_j>| <= A^2,                      (HRP25)
max_i sum_j |<z_i,z_j>| <= K^2,                      (HRP26)
```

then `(HRP7)`, `(HRP12)`, and `(HRP20)` hold with these `A,K`.

The graph-norm version holds after replacing `z_i` by `zhat_i` in
`(HRP26)`.

**Proof.**  Both Gram matrices are real symmetric and positive semidefinite.
The Schur bound, equivalently the symmetric maximum-row-sum bound, gives

```text
||G_Q||_op<=max_i sum_j |(G_Q)_(i,j)|,
||G_Z||_op<=max_i sum_j |(G_Z)_(i,j)|.               (HRP27)
```

Since `||T||^2=||G_Q||_op` and `||Z||^2=||G_Z||_op`, Theorems 1 and 2
apply.  End proof.

This is where locality enters.  Suppose every `q_i` has uniformly bounded
coefficients and support, and each support intersects only uniformly many
other packet supports.  Then each row of `G_Q` has only boundedly many
nonzero entries of bounded size, proving `(HRP25)`.  The same statement for
the integral lifts proves `(HRP26)`.  Harmonic rank may grow without changing
either constant.

Merely bounding each individual `||q_i||` is insufficient: with rank `r`, it
only gives the crude estimate `||T||<=sqrt(r) max_i||q_i||`.  Bounded overlap,
or another direct Gram-operator estimate, is the ingredient that removes
this artificial `sqrt(r)` loss.

## 5. Finite exceptional family

Let all but finitely many charts admit packet bases with the same constants
`A,K`.  Every exceptional finite-rank exact sequence has a positive dual
systole and an integral section of finite norm.  Taking the minimum and
maximum over the exceptional set therefore yields global constants

```text
inf_X B_X lambda_1(Q_X^#)>0,
sup_X kappa_X<infinity.                              (HRP28)
```

Hence a controlled finite family, such as a special level-`53` packet, does
not obstruct a family theorem.

## 6. Meaning for the projective program

The level-`121` result says that seven new directions are collectively safe;
it does not exhibit a uniform family basis.  Theorems 1--3 identify the
stronger explanation one should now seek:

1. construct a `Z`-basis of the projected harmonic cycle lattice from local
   modular-symbol or cell packets;
2. prove a level-independent bound on the absolute row sums of its Gram
   matrix;
3. lift the dual packet basis through `(HRP13)` by integral local packets;
4. prove the analogous row-sum bound for the Euclidean or graph lift Gram
   matrix.

Steps 1--2 imply the requested uniform product
`B_X lambda_1(Q_X^#)>=c>0`.  Steps 3--4 are stronger: they uniformly bound
the lift ratio on every class, and therefore in particular on every class
with `B_X||u||<1`.

The rank-two function-lattice model at level `53`, the rank-seven safety at
level `121`, and resolution-invariance of decoder bounds make such a packet
description plausible.  Establishing it for the entire projective family is
the remaining theorem, not a consequence of the finite computations.
