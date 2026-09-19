# The Bernoulli and Clifford crossed products are the two central summands of one lamp group

Date: 2026-08-14

## 1. The lamp group

Let `X` be a `G`-set (below `X=G/Gamma` for an infranormal nonnormal Kazhdan
pair).  Define the **Clifford lamp group**

```text
C(X) = < c_x (x in X), z |  z^2=1, z central,
                            c_x^2=1,
                            c_x c_y = z c_y c_x  (x != y) >.   (CLS1)
```

Every element of `C(X)` is `z^e c_(x_1) ... c_(x_k)` for a finite subset
`{x_1<...<x_k}` and `e in {0,1}`, so `C(X)` is a central `C_2`-extension

```text
1 -> <z> -> C(X) -> directSum_X C_2 -> 1,                      (CLS2)
```

and `G` acts by `g.c_x = c_(gx)`, `g.z = z`.  Put `W = (directSum_X C_2)
semidirect G` (the Kun--Thom wreath group) and
`W~ = C(X) semidirect G`, so `W~ / <z> = W`.

## 2. The decomposition

Since `z` is central of order two and `G`-fixed, `p_± = (1 ± z)/2` are
central projections of `L(W~)` of trace `1/2`.

**Proposition.**  Trace-preservingly, after rescaling each corner trace by
`2`,

```text
L(W~) = L(C(X) semidirect G)
      = ( L^infty({-1,1}^X) crossed_product G )
        (+) ( Cl(X) crossed_product G ).                        (CLS3)
```

*Proof.*  `L(W~) = L(C(X)) crossed_product G`.  On the corner `p_+` the
relation `z=1` holds, so the corner is the group von Neumann algebra of
`C(X)/<z> = directSum_X C_2`, i.e. `L^infty({-1,1}^X)` with the product
measure, and the residual `G`-action is the generalized Bernoulli shift.  On
the corner `p_-` the relation `z=-1` holds, so the `c_x` are anticommuting
self-adjoint unitaries with `tr(c_(x_1)...c_(x_k))=0` for `k>=1`: this is the
tracial Clifford (CAR) algebra `Cl(X)`, hyperfinite and, for `X` infinite,
the hyperfinite `II_1` factor.  Both corners are `G`-invariant because `G`
fixes `z`, so the crossed product splits along them.  End proof.

## 3. Consequence for the two Connes-embedding targets

Compressions of Connes-embeddable tracial algebras are Connes embeddable,
and a direct sum of two Connes-embeddable tracial algebras is Connes
embeddable (place them in complementary corners of `R^omega`).  Hence

```text
W~ is hyperlinear
   <=>  L(W) = L^infty({-1,1}^X) crossed_product G  is Connes embeddable
        AND  Cl(X) crossed_product G  is Connes embeddable.     (CLS4)
```

Consequences to record:

* the graph's two targets, `hyperlinear-wreath-model` (Bernoulli) and
  `kun-thom-clifford-crossed-product-ce` (Clifford), are **independent**:
  neither implies the other, and they are jointly equivalent to
  hyperlinearity of the single group `W~`;
* in particular `W` is hyperlinear as soon as `W~` is, even though `W` is a
  *quotient* of `W~`.  Hyperlinearity does not pass to quotients in general;
  it does here because a central `C_2` makes the quotient's group algebra a
  direct summand rather than a quotient algebra;
* the diagonal-normalizer sharpening of
  `notes/TRUE_DIAGONAL_NORMALIZER_RIGIDITY.md` applies **only to the Bernoulli
  summand**.  Its Lemma 2 (abelian diagonalization) needs the fixed algebra to
  be abelian, and `Cl(X)` is a `II_1` factor, so no conjugation puts it inside
  a diagonal ultraproduct.  Kun--Thom Definition 2.2 and Corollary D, which
  are statements about p.m.p. actions, therefore have no purchase on the
  Clifford summand at all.  The Clifford target is obstructed only through the
  repository's own radical-phase detector, not through Corollary D;
* conversely, Kun--Thom Theorem A's endgame transcribes verbatim to `W~`:
  `c_(Gamma)` commutes with `sigma(Gamma)` because `Gamma` fixes the coset
  `Gamma`; Theorem 4.1 would put `c_(t Gamma)` in the same centralizer; and
  `sigma(gamma) c_(t Gamma) sigma(gamma)^(-1) = c_(gamma t Gamma) !=
  c_(t Gamma)`.  So `W~` is nonsofic for the same reason `W` is.  (This
  overlaps `kun-thom-clifford-radical-phase`, which is where it is owned.)

## 4. Scope

Proved here: the Proposition and `(CLS4)`.  The observations in Section 3 are
immediate corollaries.  Nothing here bears on whether either summand is
Connes embeddable.
