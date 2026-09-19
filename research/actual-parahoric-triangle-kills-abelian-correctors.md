---
rg: 2
id: actual-parahoric-triangle-kills-abelian-correctors
kind: claim
title: The signed Weyl triangle on the actual forty-two-point parahoric atlas kills every abelian corrector
artifacts:
  - research/artifacts/sl3-parahoric-triangle-unimodular-certificate-2026-08-21.md
distinct_from:
  coxeter-hexagon-admits-flat-affine-corrector: that uses substitute vector stabilizers and exhibits a mod-two flat gauge; this proves that the six actual dyadic parahorics rule out that entire abelian mechanism.
  native-sl3-edge-parahoric-has-index-forty-two: that computes the atlas and its root depths; this computes the integral relation module carried by that atlas.
  rank-two-weyl-triangle-is-first-apartment-gauge-detector: that kills one already-common commutant corrector by a three-term calculation; this permits a different corrector at every parahoric point and proves covariance plus all translated triangle relations still kill them when they commute.
---

Let

```text
C=SL_3(Z),
D=C cap hCh^-1,
X=C/D,                         |X|=42.                  (APT1)
```

Let `s_12,s_23 in C` be the signed simple Weyl representatives and write
`e_x` for the standard basis of the integral permutation module `Z[X]`.
Put

```text
r=e_D-e_(s_12D)-e_(s_23D).                              (APT2)
```

Then

```text
Z[C] r = Z[X].                                          (APT3)
```

More strongly, forty-two explicit elementary translates of `r` form a
unimodular basis of `Z[X]`: their coefficient matrix has determinant `1`.
The exact finite certificate is reproduced by the dependency-free integer
script in the attached artifact.  It enumerates the `42` lattices in the
orbit of

```text
4Z e_1 directSum 2Z e_2 directSum Z e_3
```

modulo four, selects translates by Gaussian elimination modulo two, and
verifies their signed integer determinant by the Bareiss algorithm.

## Exact corrector consequence

Let `M` be any abelian `C`-module and suppose `z in M` is fixed by `D`.
The covariant family

```text
z_(gD)=g.z                                               (APT4)
```

is well defined.  If the rank-two corrector triangle holds,

```text
z_D-z_(s_12D)-z_(s_23D)=0,                              (APT5)
```

then `z=0`.  Indeed `(APT4)` defines a `C`-module map
`Z[X]->M`, and `(APT5)` says it kills `r`; `(APT3)` says it kills the whole
permutation module.

Equivalently, for a commuting family of unitary correctors, exact parahoric
centrality, actor covariance, and every conjugate of the signed Weyl triangle
force every corrector to be the identity.  The mod-two affine translation
in `coxeter-hexagon-admits-flat-affine-corrector` survives only because its
three vector stabilizers are not the actual index-forty-two groups `D_w`.

## Dimension-free robust form

Because the certificate matrix is unimodular, its inverse has fixed integral
entries.  In a commuting unitary model, each coordinate corrector is
therefore a fixed product of integer powers of the forty-two translated
triangle defects.  Word telescoping gives one finite constant `A_tri` such
that

```text
max_(x in X)||Z_x-I||_2
 <= A_tri (triangleDefect+covarianceDefect).             (APT6)
```

The constant depends only on the fixed `42`-point certificate, never on
matrix dimension or multiplicity.  Thus the actual atlas supplies the
desired constant-HS corrector collapse throughout the **abelian/commuting
gauge sector**.

The same certificate also controls the almost-commuting sector.  To state
this without hiding a choice of word order, fix the forty-two translates
`r_j` used by the certificate and write

```text
T_j(Z)=Z_(x_j) Z_(y_j)^-1 Z_(z_j)^-1                  (APT7)
```

for the corresponding ordered triangle words.  Put

```text
epsilon_tri  = max_j ||T_j(Z)-I||_2,
epsilon_com  = max_(x,y in X) ||[Z_x,Z_y]-I||_2.       (APT8)
```

If the `Z_x` are obtained from one base corrector by approximate actor
transport, let `epsilon_cov` denote the largest covariance error needed to
replace a transported triangle by the corresponding word `(APT7)`.  There
is a numerical constant `B_tri<infinity`, depending only on the displayed
forty-two-word certificate, such that

```text
max_(x in X) ||Z_x-I||_2
 <= B_tri (epsilon_tri+epsilon_cov+epsilon_com).        (APT9)
```

### Proof of `(APT9)`

Let `M` be the signed integer matrix whose rows are the vectors `r_j`.  The
certificate says `det(M)=1`, so every standard basis vector has an integral
expression

```text
e_x=sum_j a_(xj) r_j,             a_(xj) in Z.          (APT10)
```

Replace each additive symbol in `(APT10)` by its corrector unitary, keeping
one fixed order.  The product of the corresponding powers of `T_j(Z)` is
`epsilon_tri sum_j |a_(xj)|`-close to the identity by bi-invariance and word
telescoping.  In the free abelian group, collecting its letters gives
exactly `Z_x`.  Performing the same collection in the unitary group requires
only a fixed finite number of adjacent swaps, because `X`, `M^-1`, and all
the exponents in `(APT10)` are fixed.  A swap of two unitary letters costs

```text
||UV-VU||_2=||[U,V]-I||_2,                             (APT11)
```

and swaps involving inverse powers cost at most a fixed multiple of
`epsilon_com`.  Approximate actor transport contributes the fixed finite
multiple of `epsilon_cov`.  Taking the maximum of these finitely many word
length and swap counts over `x in X` gives `B_tri` and proves `(APT9)`.

Consequently a correction gauge which moves some atom by at least `rho`
must pay

```text
epsilon_tri+epsilon_cov+epsilon_com >= rho/B_tri.       (APT12)
```

Thus, once the native triangle and covariance defects vanish, every
surviving corrector escape has a **fixed noncommutative commutator floor**.
It cannot be a sequence of increasingly flat torus gauges whose
noncommutativity disappears in normalized Hilbert--Schmidt norm.

Without an estimate on `epsilon_com`, the argument cannot reorder the
correctors.  Consequently the remaining corrector-gauge obstruction has
been narrowed from arbitrary flat affine holonomy to a genuinely
nonabelian relation-module problem.  Any counterarchitecture after `(APT9)`
must retain nontrivial commutator layers; an abelian conductor translation,
torus-valued cocycle, or asymptotically commuting deformation is no longer
an escape.

There is also an exact group-theoretic strengthening.  Abelianizing the
group generated by a covariant corrector family gives precisely the module
calculation above, so that abelianization is trivial.  A nontrivial solvable
group cannot be perfect.  Hence every exact **solvable** (in particular,
nilpotent) corrector family satisfying the actual parahoric covariance and
all signed triangle relations is trivial.  The residual exact enemy must be
nonsolvable; robust control beyond the commuting sector still requires new
noncommutative input.
