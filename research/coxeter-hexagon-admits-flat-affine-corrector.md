---
rg: 2
id: coxeter-hexagon-admits-flat-affine-corrector
kind: claim
title: The Coxeter hexagon admits a flat nonconstant affine corrector with independent lamp overlap
distinct_from:
  three-parahoric-weyl-triangle-has-affine-gauge-countermodel: that gives the eight-site finite group and the three positive coweight directions; this identifies its mod-two affine map as a flat corrector on the full six-oriented Coxeter gallery.
  six-edge-holonomy-energy-ledger-is-scale-free: that charges a decoded corrector with nontrivial carrier holonomy; this proves that the Weyl, inverse, and coweight relations alone do not force such holonomy.
  six-chamber-a2-holonomy-closes-fixed-clock-sector: that kills the gauge after all chambers lie in one finite Chevalley coefficient reservoir; this keeps only directional parahoric covariance and exhibits the nonconstant flat gauge which common-reservoir extraction must eliminate.
---

Let

```text
Lambda={(a_1,a_2,a_3) in Z^3:a_1+a_2+a_3=0}            (FAC1)
```

be the `A_2` coweight lattice and let `W=S_3` permute coordinates.  Reduction
modulo two is a `W`-equivariant homomorphism

```text
bar:Lambda -> L=F_2^3.                                  (FAC2)
```

It therefore extends to a homomorphism of affine Weyl groups

```text
Psi:Lambda rtimes W -> L rtimes GL_3(F_2),
(lambda,w) |-> (bar(lambda),w).                         (FAC3)
```

Interpret the directional corrector for `lambda` as translation

```text
Z_lambda=t_(bar(lambda)).                               (FAC4)
```

Then all corrector equations inherited from the affine Weyl group hold
exactly:

```text
Z_(lambda+mu)=Z_lambda Z_mu,
w Z_lambda w^-1=Z_(w lambda),
Z_(-lambda)=Z_lambda^-1.                                (FAC5)
```

In particular the three coweight directions used by the rank-two relation
satisfy

```text
Z_lambda Z_mu^-1=Z_(lambda-mu),                         (FAC6)
```

and the alternating six-edge gallery

```text
123 -> 213 -> 231 -> 321 -> 312 -> 132 -> 123           (FAC7)
```

has exactly trivial corrector holonomy.  This is not because the corrector
is constant: for `lambda=(1,0,-1)`, `bar(lambda)=(1,0,1)!=0`.

The construction is realized inside the finite affine lamp group from
`three-parahoric-weyl-triangle-has-affine-gauge-countermodel`,

```text
H=(direct_sum_(x in L) C_2) rtimes (L rtimes GL_3(F_2)). (FAC8)
```

The translation `Z_lambda` commutes with the stabilizer of
`bar(lambda)`, and the stabilizers and correctors are transported by `W`.
Thus the six oriented chambers (opposite orientations coincide modulo two,
as required by the inverse law) carry exact local parahoric covariance,
exact Weyl transport, the exact rank-two coweight relations, and zero closed
gallery holonomy.

Nevertheless, if `P` is the half projection of the lamp at `0`, then

```text
Q_lambda=Z_lambda P Z_lambda^*,
tr(P)=tr(Q_lambda)=1/2,
[P,Q_lambda]=0,
tr(PQ_lambda)=1/4.                                      (FAC9)
```

Hence a closed hexagon can be **flat and nonconstant** while retaining the
maximally interior four-atom profile.  The inequality in
`six-edge-holonomy-energy-ledger-is-scale-free` charges a role-rotating
holonomy once supplied; `(FAC1)--(FAC9)` prove that local parahoric
covariance plus every affine-Weyl/coweight circuit does not supply it.

The finite model fails at exactly the known mixed input.  If a coefficient
root element `u` does not stabilize `bar(lambda)`, then

```text
Z_lambda u Z_lambda^-1
 =t_(bar(lambda)+u bar(lambda)) u,                      (FAC10)
```

with a nonzero translation tail.  Therefore the arithmetic decoder must use
a transverse root word outside the directional parahoric to show that the
tail either vanishes on a common finite multiplicity reservoir or exits a
conductor band.  Raw hexagon closure, even for all six corners, cannot do
that work.
