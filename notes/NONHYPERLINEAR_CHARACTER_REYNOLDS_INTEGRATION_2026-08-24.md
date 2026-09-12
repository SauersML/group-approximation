# Character universality, Reynolds atoms, and the non-hyperlinear frontier

Date: 2026-08-24

## Status

This integration does **not** prove that a non-hyperlinear group exists.  It
records two exact reductions, two source-class firewalls, and the remaining
finite compiler gates without turning any of them into assertions.

The shortest known terminal route in Cairn remains
`perfect-lcs-gap-implies-nonhyperlinear`: a perfect commuting LCS solution
together with a strict finite-dimensional gap gives a non-hyperlinear
solution group.  The narrow upstream hole on that branch is
`zpc-readable-control-freezing-to-lcs`.

## 1. The factor-character implication is valid

Chifan--Drimbe--Ioana prove that, for every acylindrically hyperbolic group
`H` and every separable tracial von Neumann algebra `M`, there are a `II_1`
factor `Q`, a trace-preserving inclusion `M subset Q`, and a representation

```text
pi:H -> U(Q),                    pi(H)''=Q.             (CRI1)
```

Take `M` non-Connes-embeddable.  If the extremal character

```text
chi(h)=tau_Q(pi(h))                                      (CRI2)
```

is forced to be regular, then its GNS factor identifies
trace-preservingly with `L(H)` (or with the group factor of the faithful
image after dividing by `ker(pi)`).  Since `Q` contains the non-CE algebra
`M`, this makes the resulting group non-hyperlinear.  Cairn records the
abstract implication in
`factor-universality-character-rigidity-implies-nonhyperlinear` and the
kernel-optimal version in
`cdi-character-rigid-image-quotient-is-an-exact-bridge`.

This is a conditional reduction, not a theorem that the CDI factor is a
group factor.  CDI explicitly leave embedding universality of actual group
factors open.

Primary source: I. Chifan, D. Drimbe, and A. Ioana,
[*Embedding universality for II1 factors with property (T)*](https://arxiv.org/html/2205.07442v1),
Theorem A(1) and Remark 1.1.

## 2. The Caprace--Thom version boundary is load-bearing

The supplied character splice cites arXiv:2606.27993 as proving

```text
Char_ext(Gamma)={delta_e,1}.                             (CRI3)
```

That statement occurs in arXiv **v1**, Theorem D.  It is not a theorem of
the current source.  The current version is v2, dated 17 July 2026 and
described by arXiv as “completely rewritten with new co-author.”  It proves
that the relevant compact-hyperbolic Caprace--Remy lattices have only the
two trivial ergodic invariant random subgroups.  In Remark 5.4 it says that
absence of nontrivial characters merely “seems plausible” and identifies an
unchecked square-integrability condition needed by the proposed argument.

Therefore v1 cannot be used as the unconditional character-rigidity input
to `(CRI1)--(CRI2)`.  Cairn records this in
`caprace-thom-v2-leaves-km-character-rigidity-open` and uses it as a required
input to the CDI permanence firewall.

Primary source: P.-E. Caprace and A. Thom,
[*On the Howe--Moore property for automorphism groups of buildings*, v2](https://arxiv.org/html/2606.27993v2),
Corollary 5.3 and Remark 5.4.  The superseded statement is visible for audit
in [v1](https://arxiv.org/html/2606.27993v1), Theorem D.

## 3. The two Kac--Moody labels do not splice the source classes

Caprace--Hume prove acylindrical hyperbolicity for **orthogonal forms** of
Kac--Moody groups acting on an irreducible non-spherical non-affine
building.  Caprace--Remy's finitely presented simple Kazhdan examples used
in the compact-hyperbolic lattice discussion are a different construction:
they occur as irreducible twin-building lattices.  Neither cited source
identifies an orthogonal form with one of those lattices or proves the
character theorem required for an orthogonal form.

Thus “Kac--Moody” is not a permanence principle transporting the CDI source
hypothesis to the proposed rigid lattice.  Cairn records the positive
orthogonal-form theorem in
`orthogonal-kac-moody-forms-are-acylindrically-hyperbolic` and consumes it in
`standard-permanence-does-not-rigidify-the-cdi-image`.

Primary source: P.-E. Caprace and D. Hume,
[*Orthogonal forms of Kac--Moody groups are acylindrically hyperbolic*](https://aif.centre-mersenne.org/articles/10.5802/aif.2998/).

There is a second, correctly narrower obstruction.  Glasner--Hase prove that
every acylindrically hyperbolic group admits a weakly mixing, nontrivial,
faithful IRS.  Its fixed-point character is faithful and nonregular.  This
rules out the naive statement that every faithful character of a CDI source
is regular.  It does **not**, without an additional factoriality argument,
refute a statement restricted to faithful **extremal** characters.  That
scope distinction is recorded in
`faithful-irs-blocks-naive-ah-character-rigidity` and is why the surviving
CDI target remains the extremal-character classification of the actual
representation image.

Primary source: Y. Glasner and A. Hase,
[*Faithful invariant random subgroups in acylindrically hyperbolic groups*](https://doi.org/10.1112/blms.12817),
Theorem 3.4.

## 4. Boolean predicate decoding is no longer the Reynolds bottleneck

For commuting involutions `x_1,...,x_k`, an independent central involution
`J`, and an assignment `a in F_2^k`, put

```text
H_a=<x_i J^(a_i):1<=i<=k>,          Q_-=(1-J)/2.
```

Then

```text
e_(H_a) Q_-
 = product_i (1+(-1)^(a_i)x_i)/2 Q_-.                  (CRI4)
```

The right side is the joint spectral atom for `a` on the negative central
sector.  Thus every forbidden assignment of an arbitrary Boolean predicate
is already an ordinary finite-subgroup Reynolds projection.  Cairn proves
this in `central-sign-bcs-atoms-are-subgroup-reynolds-projections` and also
computes its canonical density

```text
tau(e_(H_a)Q_-)=2^(-(k+1)).                             (CRI5)
```

in `central-sign-reynolds-atoms-have-fixed-canonical-density`.

The obstruction is orientation, not atom naming.  For an HNN edge induced
by an injection `K->H`, the canonical regular trace necessarily has

```text
tau(e_H)=1/|H| <= 1/|K|=tau(e_K).                       (CRI6)
```

Any selected-sector reverse gap therefore carries compensating regular
mass elsewhere.  One edge cannot remove it; a finite cycle admits a
stationary nonnegative compensation flow.  An exact trace-functorial
infinite ladder cannot solve the problem either, because Cairn's
`exact-first-hit-ladder-kills-regular-carrier` applies in `L(Gamma)`.

The live target `central-sign-reynolds-first-hit-compiler` is consequently
matrix-specific: use the strict finite-dimensional BCS gap to select the
companion multiplicity, route successive copies into summable orthogonal
first-hit layers, and retain an exact infinite completion in which the
regular compensation can flow.  Once this compiler provides fixed
`q_*,eta>0`, `branching-plus-first-hit-exits-forces-hs-floor` gives

```text
eta N q_* <= 1 + controlled presentation error,         (CRI7)
```

and a sufficiently large fixed depth yields a normalized-HS defect floor.
No unconditional groupification is asserted here.

## 5. Current compressed frontier

The following named gates remain open and must remain displayed as such:

- `zpc-readable-control-freezing-to-lcs`;
- `atlas-five-row-operator-phase-lift`;
- `binary-schur-toeplitz-one-branch-hs-payment`;
- `quantized-scale-index`;
- `marked-swap-star-compiler`;
- `cdi-image-quotient-off-regular-characters-are-ce`;
- `central-sign-reynolds-first-hit-compiler`.

The first is the cleanest perfect-LCS endgame.  The last is the precise
first-hit compensation version of the Reynolds architecture.  The CDI node
is the exact canonical-trace promotion problem after quotienting the actual
representation kernel.  None is discharged by the literature audited
above.
