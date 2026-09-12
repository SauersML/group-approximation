---
rg: 2
id: aggregate-leaf-bessel-fails-after-prefix-transport
kind: claim
title: Aggregate leaf Bessel bookkeeping fails after prefix transport, and left multiplication does not repair it
distinct_from:
  fct8-left-lift-and-rotated-defect-firewall: that compares the rank-one and left-multiplier lifts for the concrete free-compressor tree and gives an exact exponential rotated-defect packet; this proves the general fixed-error Bessel/frame criterion and adds a genuine canonical one-compressor property-(T) countermodel to compressed-to-full invariance.
  free-compressor-tree-has-constant-first-hit-mover-mass: that constructs the orthogonal Bernoulli leaves and isolates a desired depth-uniform Reynolds estimate; this proves the elementary aggregate error estimate cannot supply that row after leaf-dependent prefix conjugation and audits the left-multiplication amplifier.
  property-t-hs-positive-density-commutant-no-growth: that controls positive normalized adjoint dimension for one common compressed Kazhdan copy; this shows why orthogonal physical leaf mass does not produce such a common adjoint subspace.
  kt-single-compressor-canonical-lamps-do-not-exactify-actor: that proves the canonical one-compressor actor maps cannot be corrected to exact representations; this extracts the direct single-projection countermodel to approximate compressed-to-full invariance and combines it with the aggregate transport obstruction.
---

**ESTABLISHED FIREWALL.** Let `(X_i)_(i in I)` be pairwise orthogonal
projections in `M_d` with `P=sum_i X_i<=I`. For every matrix `E`, normalized
Hilbert--Schmidt Pythagoras gives the exact estimate

```text
sum_i ||E X_i||_2^2
 =tr_d(E^* E P)
 <=||E||_2^2.                                           (ALB1)
```

The same estimate holds for right multiplication. It is dimension-free and
has no cardinality loss.

It does **not** survive the prefix transports needed in the compressor tree.
If `E_i=U_i E U_i^*`, then the relevant identity is instead

```text
sum_i ||E_i X_i||_2^2
 =tr_d(E^* E sum_i U_i^* X_i U_i).                     (ALB2)
```

The transported projections need not be orthogonal. For the sharp example
take `d=N`, `X_i=e_(ii)`, `E=e_(11)`, and let `U_i` send the first coordinate
to the `i`-th coordinate. Then `E_i=X_i`, so

```text
||E||_2^2=1/N,
sum_i ||E_i X_i||_2^2=1.                               (ALB3)
```

Equivalently, all transported projections `U_i^*X_iU_i` equal `e_(11)`.
Thus a vanishing relator wall can be rotated into every orthogonal leaf and
acquire order-one aggregate mass. This is exactly the change of coordinates
from `H_v=v Gamma v^(-1)` to a common copy of `Gamma`: the fixed source
relator error becomes its leaf-dependent conjugate by the prefix word `v`.

The precise sufficient replacement for orthogonality is the transported
frame bound

```text
sum_i U_i^* X_i U_i <= C I.                            (ALB4)
```

Under `(ALB4)`, `(ALB2)` is at most `C||E||_2^2`. Without such a bound, a
finite-presentation ledger and property `(T)` alone cannot perform the
aggregate promotion.

## Property (T) already has a one-leaf countermodel

This is not only a free-matrix bookkeeping issue. Take one positive strict
Kun--Thom compressor `t`, put `V=<Gamma,t>`, and use the canonical permutation
microstates of

```text
W_t=(directSum_(V/Gamma) C_2) semidirect V.
```

They exist by `kun-thom-single-compressor-sofic-joint-nonsofic`. Let `l_x` be
the binary lamp at `x=t Gamma` and put

```text
X_n=(I-phi_n(l_x))/2.
```

The stabilizer `t Gamma t^(-1)` fixes `x`, so `X_n` is asymptotically fixed
under its finite Kazhdan generating set. Choose
`gamma in Gamma\t Gamma t^(-1)`. Then `gamma x != x`; the canonical Bernoulli
trace gives

```text
||phi_n(gamma)X_n phi_n(gamma)^*-X_n||_2^2 -> 1/2.     (ALB5)
```

This is already an orthogonal family with one member and sum at most one.
Hence no implication from approximate `H_w`-invariance to approximate
`H_v`-invariance follows from property `(T)` and the one-compressor group
relations. Any proof using a finite relation fragment is refuted by these
canonical microstates, which asymptotically satisfy every fixed finite
fragment. This does not refute a theorem using the simultaneous incompatible
two-compressor tables; it proves that those extra relations, rather than
aggregate Bessel bookkeeping, must do the work.

## The left-multiplication amplifier is isometric but circular

On the Hilbert space `M_d`, let `L_X(Y)=XY` and let
`C_U(Y)=UYU^*`. With normalized trace on `B(M_d)=M_(d^2)`, one has

```text
tr_(d^2)(L_X)=tr_d(X),
L_X L_Y=L_(XY),
C_U L_X C_U^*=L_(UXU^*),
||L_X-L_Y||_(2,d^2)=||X-Y||_(2,d).                    (ALB6)
```

Thus orthogonal leaves become orthogonal projections of the advertised
macroscopic superoperator trace, and their conjugation defects are preserved
exactly. But `(ALB2)--(ALB3)` are also preserved exactly: prefix transport
sends `L_(X_i)` to `L_(U_i^*X_iU_i)`, whose sum can have norm `N`.

Moreover, if a relator evaluates to `R in U(d)`, then

```text
||C_R-I||_(2,d^2)^2
 =2(1-|tr_d(R)|^2)
 <=2||R-I||_(2,d)^2.                                  (ALB7)
```

So the amplified one-compressor countermodel still has vanishing relator
defect and the same fixed mover defect. The apparent rank gain does not meet
the positive-adjoint-density hypothesis: `L_X` is one vector in
`L^2(M_(d^2))`. Its operator rank does not create a pointwise fixed subspace
of that dimension. The range of `L_X` is merely invariant when `L_X`
commutes with the adjoint actor; its vectors are not fixed individually.
Applying left multiplication again only repeats this distinction.

Therefore neither `(ALB1)` nor the map `X->L_X` proves the desired
depth-uniform aggregate Reynolds inequality. The live additional datum is a
uniform transported-frame/common-Cartan bound such as `(ALB4)`, or a genuinely
joint two-compressor classicalization theorem.

DERIVATION
aggregate-prefix-transport-firewall-proof
