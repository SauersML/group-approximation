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

**Theorem (complete finite-dimensional tangent sterility).**  Assume both
`G` and `Gamma` have property `(T)` and

```text
t Gamma t^(-1)<=Gamma,       h=t^(-1) gamma t.
```

For every finite-dimensional unitary representation

```text
rho:D=G *_Gamma G -> U(d)
```

and every unitary Zariski tangent `b` at `rho`,

```text
b(i_2(h)i_1(h)^(-1))=0.                              (QRJ12)
```

**Proof.**  Write `rho_j` and `b_j` for the restrictions to the two vertex
copies.  Since the marked word belongs to the sofic radical and `rho(D)` is
sofic,

```text
rho_1(h)=rho_2(h)=H.                                 (QRJ13)
```

The tangent is a `1`-cocycle for the finite-dimensional unitary adjoint
representation.  Property `(T)` gives `H^1(G,Ad rho_j)=0`, so there are
skew-Hermitian `X_j` with

```text
b_j(g)=X_j-Ad(rho_j(g))X_j.                          (QRJ14)
```

The two cocycles agree on the amalgamated subgroup.  Since the two
representations also agree there, `Y=X_2-X_1` intertwines the restrictions
of `rho_1` and `rho_2` to `Gamma`.  The finite-intertwiner propagation lemma
then says

```text
rho_1(h)Y=Y rho_2(h).
```

Using `(QRJ13)`, this is `[Y,H]=0`.  The cocycle rule and `(QRJ14)` now give

```text
b(i_2(h)i_1(h)^(-1))
 =b_2(h)-b_1(h)
 =Y-Ad(H)Y
 =0.
```

This proves `(QRJ12)`.  End proof.

A cocycle which vanishes on this fold difference also vanishes on every
conjugate and product of its conjugates.  Therefore the normal closure of
the marked primitive radical word is tangent-zero at every
finite-dimensional unitary point.  The complete sofic radical is generated
by fold differences for all elements of the normal closure of `Gamma`; the
argument above is asserted only for the displayed inverse-predecessor
family, not automatically for every one of those generators.

Thus the new criterion does not merely fail on the same-model folded
ansatz: the whole finite-dimensional representation scheme of this double
is tangent-sterile on the marked radical direction we need.  A successful
use of the criterion must change the radical presentation, or leave honest
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
