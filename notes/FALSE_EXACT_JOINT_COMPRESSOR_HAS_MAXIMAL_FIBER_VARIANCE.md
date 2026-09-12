# Exact joint compressor covariance permits maximal fiber variance

Date: 2026-08-14

## 1. Outcome

The single-compressor construction in
`TRUE_ONE_COMPRESSOR_JOINTLY_RECOVERS_BOTH_OUTER_TRANSITIONS.md` produces one
intrinsic joint extension-character PVM.  That synchronization is exact and
useful, but it cannot by itself produce the finite-window endomorphism
decoder.  There is an elementary finite-dimensional countermodel in which

```text
joint covariance defect = 0,
joint transition variance = 0,
left/right transition measurements share one fine PVM,
binary extension-fiber conditional variance = 1/4.       (JCV1)
```

The last value is the maximum possible variance of a binary projection.
The countermodel works for every proper inclusion of finite binary additive
packets.  It also iterates along arbitrary finite chains.  Consequently,
neither larger coefficient windows nor repeated use of the same compressor
can turn joint covariance alone into the missing decoder.

This does not refute the Leavitt route.  It proves that its remaining input
must be a **mixed multiplication constraint** coupling the two outer
characters, not another Fourier/covariance refinement.

## 2. The exact one-edge model

Let `F,G` be finite abelian groups and let

```text
alpha:F -> G                                             (JCV2)
```

be injective.  Write `G^` for the character group of `G` and put

```text
H=l2(G^).
```

For `psi in G^`, let `e_psi` be the standard basis vector and define

```text
sigma(g)e_psi = psi(g)e_psi,
rho(a)e_psi   = psi(alpha(a))e_psi.                     (JCV3)
```

Thus `rho=sigma o alpha` on one and the same finite-dimensional Hilbert
space.  With compressor `U=1`, covariance is exact:

```text
U rho(a) U* = sigma(alpha(a))             (a in F).    (JCV4)
```

Let `E_psi` be the rank-one projection onto `e_psi`.  The target character
PVM is `(E_psi)`, while the source character projection at `chi in F^` is

```text
P_chi=sum_(psi restricted along alpha = chi) E_psi.    (JCV5)
```

Hence the intrinsic transition effects are already projections and the
rounded fine transition PVM is literally `(E_psi)`.  Formula `(JCV5)` is
exactly the many-to-one extension-character decomposition targeted by the
compressor program; no gauge, perturbation, or rounding loss is present.

## 3. A maximally invisible binary branch

Assume now that `G/F` is a nontrivial binary vector space.  Every restriction
fiber in `(JCV5)` is a coset of

```text
K=ker(G^ -> F^),
```

and has the same even cardinality.  Choose a function

```text
r:G^->{0,1}                                           (JCV6)
```

which takes each value equally often on every restriction fiber, and put

```text
B=sum_(r(psi)=1) E_psi.                               (JCV7)
```

Let `A_F=W*(P_chi:chi in F^)` be the coarse source-character algebra.  In
the normalized matrix trace, fiberwise averaging gives

```text
E_(A_F)(B)=(1/2)1.                                    (JCV8)
```

Since `B` is a projection of trace `1/2`,

```text
||B-E_(A_F)(B)||_2^2
 =tau((B-(1/2)1)^2)
 =1/4.                                                (JCV9)
```

Thus the majority-decoder error from
`TRUE_BINARY_EXTENSION_FIBER_MAJORITY_DECODER.md` does not merely fail to
vanish: every fiber is tied, and the conditional variance is maximal.

## 4. The exact joint model

Apply the same construction to the product inclusion

```text
alpha x alpha:F x F -> G x G                         (JCV10)
```

on `l2(G^ x G^)`.  The two outer representations commute, their joint fine
PVM consists of the rank-one atoms `E_(psi_L,psi_R)`, and `U=1` implements
the joint covariance exactly.  The two outer measurements are literal
marginals of this one PVM, exactly as in `(JOT10)--(JOT11)`.

Choose balanced branch functions independently in the left and right
restriction fibers.  Each branch projection then satisfies `(JCV9)`, while
all of the joint covariance and PVM compatibility conclusions remain exact.
The common-compressor telescope therefore removes relative PVM gauge but
places no pressure at all on extension-fiber measurability.

## 5. Iteration does not help

For a chain of injective finite abelian groups

```text
F_0 -> F_1 -> ... -> F_n,                             (JCV11)
```

represent every `F_i` diagonally on `l2(F_n^)` by restriction of terminal
characters.  Every arrow is then implemented by the identity unitary and
all path-composition identities are exact.  At any proper binary step, a
balanced bit on the new kernel coordinate still has conditional variance
`1/4` over the preceding character algebra.

This is the finite version of the diffuse Haar/Bernoulli obstruction.  It
also corrects a possible martingale shortcut: deeper exact path coherence
does not make successive branch bits measurable from earlier sigma
algebras.  Fresh balanced bits can occur at every depth.

## 6. Corrected live gate

The countermodel realizes all conclusions which use only:

1. exact additive root representations;
2. one common proper-compressor covariance;
3. the intrinsic fine transition PVM;
4. arbitrary finite-depth functorial composition; and
5. exact joint compatibility of the two commuting outer roots.

It does **not** realize the Leavitt coefficient multiplication table.  That
is now the only available separator.  The remaining theorem should be
stated without any residual PVM language:

> **Mixed multiplication-to-variance estimate.**  For the joint outer-root
> transition PVM produced by the actual rank-five Leavitt packet, bound the
> sum of the left and right extension-fiber conditional variances by the
> normalized Hilbert--Schmidt energy of fixed mixed middle-root/compressor
> relators, with a constant independent of the finite packet and matrix
> dimension.

Equivalently, one must show that the nested identities

```text
[X_i(a),[H,Y_j(b)]]=x_14(delta_(ij) ab)              (JCV12)
```

make the balanced construction `(JCV6)--(JCV10)` impossible when the four
one-sided Leavitt maps are all represented on the common positive-density
long-root carrier.  Pure compressor covariance cannot contribute further:
it is already zero in the countermodel.

Once this estimate is proved, the existing majority decoder, whole-map PVM
classicalization, tree gluing, and robust `1/36` paired-quotient floor give
the contradiction.  No local computation or build was run for this note.
