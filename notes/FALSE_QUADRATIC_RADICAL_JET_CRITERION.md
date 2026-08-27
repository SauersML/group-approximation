# A first-order radical jet already proves FALSE

Date: 2026-08-12

## 1. Outcome

Let

```text
K=<S | R>
```

be finitely presented and let

```text
1!=q in Rad_sof(K).
```

Fix a finite-dimensional unitary representation

```text
rho:K->U(d).
```

Choose skew-Hermitian matrices `X_s`, one for each generator, and put

```text
u_s(t)=exp(t X_s)rho(s).
```

Assume that every defining relator is stationary to first order,

```text
d/dt|_(t=0) r(u(t))=0              for every r in R,   (QRJ1)
```

but the marked radical word is not:

```text
A=d/dt|_(t=0) q(u(t)) !=0.                             (QRJ2)
```

Then a hyperlinear nonsofic group exists.

Thus no integration of the tangent, no actual nonlinear branch of the
representation variety, and no positive lower bound on a marked trace are
required.  A nonreduced finite-dimensional unitary point at which the
sofic-radical word has a nonzero tangent is already a complete FALSE
certificate.

## 2. Why the radical word starts at the identity

The image `rho(K)` is a finitely generated complex linear group.  By
Malcev's theorem it is residually finite, hence sofic.  Since `q` belongs
to the full sofic radical,

```text
rho(q)=1.                                               (QRJ3)
```

Consequently `(QRJ2)` is a tangent based at the identity.  In particular
`A` is skew-Hermitian.

## 3. From a tangent to second-order almost representations

Fix once and for all a word representative `sigma(g)` in the free group
on `S` for every `g in K`, and define

```text
phi_t(g)=sigma(g)(u(t)).                                (QRJ4)
```

Condition `(QRJ1)` and Taylor's theorem give

```text
||r(u(t))-1||_2=O(t^2)              (r in R).          (QRJ5)
```

For each fixed pair `g,h`, the word

```text
sigma(g)sigma(h)sigma(gh)^(-1)
```

is a finite product of conjugates of defining relators and their inverses.
Telescoping `(QRJ5)` therefore gives

```text
||phi_t(g)phi_t(h)-phi_t(gh)||_2=O_(g,h)(t^2).         (QRJ6)
```

On the marked word, `(QRJ2)--(QRJ3)` give

```text
phi_t(q)=1+tA+O(t^2).
```

For every unitary `V`,

```text
1-Re tr(V)=(1/2)||V-1||_2^2.
```

Hence

```text
kappa(t):=1-Re tr(phi_t(q))
         =(t^2/2)||A||_2^2+o(t^2).                    (QRJ7)
```

In particular `kappa(t)>0` for all sufficiently small nonzero `t`.

Enumerate the multiplication table of `K`.  If `C_n` is a common constant
in `(QRJ6)` for the first `n` tested products, choose `t_n->0` so slowly or
quickly that

```text
C_n t_n->0.
```

Writing `eta_n` for the resulting window defect, `(QRJ6)--(QRJ7)` imply

```text
eta_n^2/kappa(t_n)=O(C_n^2 t_n^2)->0.                 (QRJ8)
```

The phase-cancelled tensor amplifier in
`FALSE_ONE_NUMBER_RELATIVE_COMMUTANT_CRITERION.md` now produces a
homomorphism from `K` to a tracial matrix ultraproduct in which `q`
survives.  Its image is hyperlinear and cannot be sofic.  This proves the
criterion.

## 4. Folded-double specialization

Let

```text
D=G *_Gamma G,
q=i_2(h)i_1(h)^(-1) in Rad_sof(D),
```

and let `rho:G->U(d)` be an honest finite-dimensional representation.
Fold the two vertex maps to the same `rho`.  Keep the first vertex fixed
and conjugate the second by `exp(tX)`.  The amalgamation relations are
stationary to first order exactly when

```text
X in rho(Gamma)'.                                      (QRJ9)
```

The marked derivative is nonzero exactly when

```text
[X,rho(h)]!=0.                                        (QRJ10)
```

Therefore one finite-dimensional relative-bicommutant escape

```text
rho(h) notin (rho(Gamma)')'                            (QRJ11)
```

would already prove FALSE.

For the strict Kun--Thom compressor pair used in this repository,
`FALSE_COMPACT_ACTION_RELATIVE_ANCHOR_NO_GO.md` proves that `(QRJ11)` never
occurs: every finite-dimensional `Gamma`-intertwiner also intertwines the
inverse predecessor `h`.

In fact the obstruction is stronger than the folded-conjugation ansatz.

**Theorem (complete finite-dimensional tangent sterility).**  Assume `G`
has property `(T)`.  Assume also that `Gamma<G` is infranormal: the
semigroup

```text
S={s in G:s Gamma s^(-1)<=Gamma}
```

generates `G`.  Put `N=normalClosure_G(Gamma)`.  For every finite-dimensional
unitary representation

```text
rho:D=G *_Gamma G -> U(d)
```

and every unitary Zariski tangent `b` at `rho`, one has

```text
b(i_2(n)i_1(n)^(-1))=0             for every n in N. (QRJ12)
```

**Proof.**  Write `rho_j` and `b_j` for the restrictions to the two vertex
copies.  Every fold difference in `(QRJ12)` belongs to the full sofic
radical, and `rho(D)` is sofic.  Hence

```text
rho_1(n)=rho_2(n)                  for every n in N. (QRJ13)
```

The tangent is a `1`-cocycle for the finite-dimensional unitary adjoint
representation.  Property `(T)` gives `H^1(G,Ad rho_j)=0`, so there are
skew-Hermitian `X_j` with

```text
b_j(g)=X_j-Ad(rho_j(g))X_j.                          (QRJ14)
```

The two cocycles agree on the amalgamated subgroup.  Since the two
representations also agree there, `Y=X_2-X_1` intertwines the restrictions
of `rho_1` and `rho_2` to `Gamma`.  On `Hom(C^d,C^d)` put

```text
beta(g)T=rho_1(g)T rho_2(g)^*.
```

Then `Y in Fix_Gamma(beta)`.  For `s in S`,

```text
beta(s)Fix_Gamma(beta)=Fix_(s Gamma s^(-1))(beta)
                      contains Fix_Gamma(beta).
```

The two spaces have equal finite dimension, so they are equal.  Since `S`
generates `G`, `Fix_Gamma(beta)` is `G`-invariant.  Every conjugate of
`Gamma` consequently fixes this space pointwise, and hence so does `N`.
Therefore

```text
rho_1(n)Y=Y rho_2(n)                 (n in N).        (QRJ15)
```

For fixed `n in N`, write the common value in `(QRJ13)` as `H_n`.
Equation `(QRJ15)` becomes `[Y,H_n]=0`.  The cocycle rule and `(QRJ14)` now
give

```text
b(i_2(n)i_1(n)^(-1))
 =b_2(n)-b_1(n)
 =Y-Ad(H_n)Y
 =0.
```

This proves `(QRJ12)`.  End proof.

The complete-radical theorem identifies `Rad_sof(D)` with the normal closure
of the fold differences in `(QRJ12)`.  A cocycle vanishing on those
generators vanishes on every conjugate and product of them.  Therefore the
evaluation map of the **entire sofic radical** has zero derivative at every
finite-dimensional unitary point of the current double.

Thus the new criterion does not merely fail on the same-model folded
ansatz: the whole finite-dimensional representation scheme of this double
is tangent-sterile in every radical direction.  A successful use of the
criterion must change the radical presentation, or leave honest
finite-dimensional base points and use genuinely nonliftable approximate
models.

## 5. Consequences for the atlas computations

The threshold change is important for the atlas program.  A tangent which
kills **all defining relators** to first order and moves the marked radical
word would now finish the problem even if every attempted nonlinear
integration is quadratically obstructed.

The currently certified outer `A_8` tangent does not yet qualify.  It kills
only the 24 perfect-overlap-certified radius-five classes.  Those are not a
presentation whose normal closure is known to contain every genuine atlas
relation, and the marked class is not proved to lie in the full sofic
radical of that partial quotient.  The large `136`-dimensional tangent
kernel and `60`-dimensional phase-moving image are therefore a real local
signal, but not a FALSE certificate under this theorem.

This changes the highest-yield finite search.  The right question is no
longer whether the outer tangent integrates.  It is whether one can attach
a finite presentation with a certified sofic-radical word to a
finite-dimensional unitary point and find a nonzero marked tangent modulo
the derivatives of **all** defining relators.  That is an exact linear
algebra problem.

## 6. Higher-order radical jets

The first-order statement is only the smallest case of the amplifier.
Suppose, for some fixed `m>=1`, smooth unitary generator paths based at a
finite-dimensional representation satisfy

```text
r(u(t))=1+O(t^(m+1))                  (r in R),       (QRJ16)
q(u(t))=1+t^m A+O(t^(m+1)),           A!=0.           (QRJ17)
```

Then the induced multiplication defect is `O(t^(m+1))`, while

```text
1-Re tr(q(u(t)))
 =(t^(2m)/2)||A||_2^2+o(t^(2m)).                     (QRJ18)
```

Consequently

```text
(multiplication defect)^2/(marked trace gap)=O(t^2). (QRJ19)
```

The same diagonalization and phase-cancelled tensor amplification prove:

**Higher-jet criterion.**  Any finite-order unitary jet for which the
sofic-radical word appears strictly before the defining-relator error gives
a hyperlinear nonsofic group.

This includes jets which are first-order tangent-zero but acquire a marked
quadratic or higher obstruction.  The relevant search is therefore for a
strict order gap, not specifically for a nonzero first derivative.

## 7. The current symmetric double is sterile to every finite order

The stronger criterion still cannot be realized at a fixed-dimensional
unitary point of the present Kun--Thom double.

**Theorem (finite-order radical-arc sterility).**  Retain the explicit
infranormal pair, and assume both `G` and `Gamma` have property `(T)`.  Let
`rho` be a finite-dimensional unitary representation of

```text
D=G *_Gamma G.
```

Suppose unitary generator paths based at `rho` make every defining relator
`O(t^(m+1))`.  Then, for every `n in N=normalClosure_G(Gamma)`,

```text
i_2(n)(u(t)) i_1(n)(u(t))^(-1)=1+O(t^(m+1)).          (QRJ20)
```

In particular no element of `Rad_sof(D)` can first appear at an order at
most `m`.

**Proof.**  Restrict the paths to either vertex copy of `G`.  We first use
the standard formal-rigidity induction.  Suppose that, after conjugating by
a unitary polynomial path, the vertex assignment agrees with its base
representation modulo `t^k`.  Its coefficient at order `t^k` satisfies the
linearized group relations, hence is a `1`-cocycle for the finite-dimensional
unitary adjoint representation.  Property `(T)` gives `H^1=0`, so this
cocycle is inner.  Conjugating by `exp(t^k X)` removes it.  Induction for
`k=1,...,m` gives unitary paths `V_j(t)`, `j=1,2`, such that

```text
u_j(g,t)=V_j(t)rho_j(g)V_j(t)^*+O_g(t^(m+1)).          (QRJ21)
```

Apply the edge relations to a finite Kazhdan set of `Gamma` and put

```text
Y(t)=V_1(t)^*V_2(t).
```

Then `Y(t)` is an `O(t^(m+1))` almost-intertwiner between `rho_2|Gamma`
and `rho_1|Gamma`.  The Kazhdan projection puts it within
`O(t^(m+1))` of an exact `Gamma`-intertwiner `Z(t)`.  Infranormal
finite-intertwiner propagation, proved in Section 4, makes `Z(t)` intertwine
every `n in N`.  Hence `Y(t)` intertwines every fixed `n in N` up to
`O(t^(m+1))`.  Substitution in `(QRJ21)` gives

```text
u_1(n,t)-u_2(n,t)=O(t^(m+1)),
```

which is `(QRJ20)`.  Since the complete sofic radical is normally generated
by these fold differences, finite telescoping gives the final assertion.
End proof.

This rules out exact Jacobian, Hessian, and all fixed-order power-series
searches at every fixed-dimensional representation of the current double.
The only surviving uses of `(QRJ19)` must have dimension growing with the
window or must use a different nonsofic radical presentation whose vertex
deformation theory is not Kazhdan-rigid.

## 8. Tangent sterility survives the standard group gadgets

The obstruction cannot be removed by repackaging the same radical word.

1. If `f:D->K` is a quotient and `q=f(r)`, every representation and every
   tangent of `K` pull back along `f`.  Hence tangent-zero of `r` on `D`
   implies tangent-zero of `q` on `K`.
2. If `D` embeds in a larger group and the marked element remains `r`, every
   tangent of the larger group restricts to one of `D`, so it still kills
   `r`.
3. For a `1`-cocycle `b` based at a representation which kills `r`, the set
   of elements in `ker(rho)` on which `b` vanishes is normal.  Indeed the
   cocycle identities preserve products and inverses, and for
   `rho(r)=1=b(r)` they give

   ```text
   b(g r g^(-1))=Ad(rho(g))b(r)=0.
   ```

   Thus every word in the normal closure of `r` is tangent-zero as well.

Consequently abelianizing the double radical, passing to bounded-exponent
lamp quotients, adding a central shear whose marked element lies in the old
normal closure, or taking another quotient of the current double cannot
create a finite-dimensional radical-moving jet.  The higher-jet criterion
must either be fed by growing-dimensional approximate points or by a source
of nonsoficity not inherited from this tangent-sterile radical.
