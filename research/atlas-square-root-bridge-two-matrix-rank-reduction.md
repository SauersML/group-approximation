---
rg: 2
id: atlas-square-root-bridge-two-matrix-rank-reduction
kind: claim
title: The square-root bridge reduces the thirteen Atlas fillings to a two-matrix rank system
distinct_from:
  atlas-q14-growing-width-rank-one-bridge-is-sharp: that proves coefficient cyclicity and exact q14; this computes the remaining thirteen residuals and identifies the precise input needed for a countermodel.
  atlas-fixed-formal-toeplitz-microstates-promote: that treats substitutions of one fixed formal Laurent symbol; the matrices X_s and Y_s here may be arbitrary genuinely nonstationary generators of growing full matrix algebras.
  atlas-m2-coefficient-substitution-cannot-dilute-q14: that substitutes an approximate M2 table into the known packet-collision escape and retains a q14 floor; here q14 is exact and the unresolved conditions are the twelve cubes plus collision.
---

ESTABLISHED.  Let `R_13` be the twelve post-q14 packet cubes and collision.
For `X,Y in M_s(F2)`, set

```text
That(X,Y)=I+E13 tensor X+E14 tensor Y in GL_(4s)(F2). (SBR1)
```

For each fixed word `w in R_13`, evaluation of the two marked natural A8
charts defines an explicit noncommutative two-matrix polynomial

```text
P_w(X,Y)=w(chart_1, That chart_1 That^(-1))-I
          in M_4(M_s(F2)).                            (SBR2)
```

Now take `k<=s`, amplify `(SBR1)` on `K=F2^k`, and add the cyclic
rank-one bridge from `atlas-q14-growing-width-rank-one-bridge-is-sharp`:

```text
T0=That(X,Y) tensor I_K,
T =T0+E24 tensor R,       rank R=1.                  (SBR3)
```

Then q14 is exact and `C_T=M_(sk)(F2)` whenever `X,Y` generate `M_s(F2)`
and the left and right `K`-coordinates of `R` span `K` and `K^*`.
Moreover, if `n_2(w)` is the number of second-chart syllables of `w`,

```text
| rank(w(T)-I) - k rank(P_w(X,Y)) | <= 2 n_2(w).     (SBR4)
```

Thus a sequence of generating pairs `X_s,Y_s in M_s(F2)` satisfying

```text
max_(w in R_13) rank P_w(X_s,Y_s)/s -> 0             (SBR5)
```

compiles at `k=s` to q14-exact repeated-natural Atlas modules of dimension
`4s^2` with every literal residual of normalized rank tending to zero and
with full coefficient algebra `M_(s^2)(F2)`.  Unless all thirteen bridged
residuals vanish exactly, any one nonzero residual image is cyclic and hence
the full relator ideal image is the whole module.  Therefore `(SBR5)`, plus
nonexactness of one bridged filling, is an explicit countermodel to
`atlas-left-ideal-rank-nonwandering`.

Conversely, a positive result on this family must prove a uniform rank
density statement for the explicit polynomials `(SBR2)`: generating pairs
cannot make all thirteen values `o(s)`-rank, except possibly by landing on
an exact augmented zero.  No bounded-width or q14 argument can replace this
two-matrix statement.

The polynomials in `(SBR2)` have a completely explicit bounded-degree
form.  Put

```text
A=E13 tensor X+E14 tensor Y,
C_b=A(b tensor I)+(b tensor I)A+A(b tensor I)A.       (SBR6)
```

Then conjugation by `That=I+A` sends `b tensor I` to
`b tensor I+C_b`.  For a packet cube `(b_2 a_1)^3`, put
`D=(b tensor I)(a tensor I)` and `H=C_b(a tensor I)`.  Since `D^3=I`,

```text
P_(a,b)=D^2H+DHD+HD^2+DH^2+HDH+H^2D+H^3.           (SBR7)
```

This has degree at most six in `X,Y`.  For collision, whose four
second-chart letters are `b_1,...,b_4` and whose interleaved first-chart
letters are fixed matrices `a_1,...,a_4`, one has

```text
P_collision=
 sum_(empty != J <= {1,2,3,4})
 product_(j=1)^4 ( (C_(b_j) if j in J else b_j tensor I)
                    (a_j tensor I) ).                (SBR8)
```

The constant term is zero by
`atlas-square-root-collision-constant-term-is-zero`: the identity alignment
is collision-zero but fails the packet.  Thus collision has degree at most
eight and no degree-zero term.  Equations
`(SBR6)`--`(SBR8)` are the induced tensor equations on `X,Y`; the bridge
vectors and covectors do not enter their leading amplified ranks at all.

### Proof of the residual formula

Because `E13,E14,E24` have pairwise-zero products, both `T0` and `T` are
self-inverse.  Evaluation at `T0` commutes with amplification, giving the
exact identity

```text
w(T0)-I=P_w(X,Y) tensor I_K.                          (SBR9)
```

Hence its rank is `k rank P_w(X,Y)`.

The whole chart changes satisfy `rank(T-T0)=1`, and their inverses differ
by rank one as well.  For any fixed second-chart syllable `b`,

```text
rank(T b T^(-1)-T0 b T0^(-1)) <= 2.                 (SBR10)
```

First-chart syllables do not change.  Telescoping the product defining `w`
and using invariance of rank under multiplication by invertibles yields

```text
rank(w(T)-w(T0)) <= 2 n_2(w).                        (SBR11)
```

The elementary inequality
`|rank A-rank B|<=rank(A-B)` proves `(SBR4)`.  Since every word in `R_13`
is fixed, the right side is independent of `s,k`.  At `k=s`, `(SBR5)` and
`(SBR4)` give `rank(w(T)-I)=o(s^2)`.  Coefficient cyclicity and exact q14
are precisely the conclusions of the square-root bridge construction.
