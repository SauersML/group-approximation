# The reflection--BS skeleton is a balanced two-channel HNN extension

Date: 2026-08-14

## 1. Outcome

Remove the two modular order-three relators from the fixed-central-sector
presentation in
`TRUE_FACTORIZED_BS14_GATE_HAS_ONE_DIHEDRAL_REFLECTION.md`, and retain the
reflection and fourth-power relations

```text
A^2=epsilon 1,
A^(-1) C A=C^(-1),
C X C^(-1)=X^4.                                      (BH1)
```

This skeleton has a more rigid structure than the cyclic-amalgam notation
suggests.  Put

```text
Y=A^(-1) X A.                                         (BH2)
```

Conjugating the last relation in `(BH1)` by `A` gives the opposite
fourth-power channel

```text
C^(-1) Y C=Y^4.                                      (BH3)
```

Before choosing the scalar `epsilon`, the corresponding central group has an
index-two core

```text
J = J_0 x <z>,

J_0=<C,X,Y |
      C X C^(-1)=X^4,
      C^(-1) Y C=Y^4>.                               (BH4)
```

The projective reflection interchanges `X` and `Y` and reverses `C`.  After
killing `z`, the skeleton is exactly

```text
J_0 semidirect_(theta) C_2,
theta(C)=C^(-1), theta(X)=Y, theta(Y)=X.              (BH5)
```

Moreover, `J_0` is a single HNN extension of the free group `F(X,Y)`:

```text
J_0 = HNN(F(X,Y), H, K, phi),                         (BH6)

H=<X,Y^4>,          K=<X^4,Y>,
phi(X)=X^4,         phi(Y^4)=Y.
```

Thus reflection-preserving `BS(1,4)` repair is an **equivariant balanced-HNN
repair problem**.  It is not two unrelated applications of `BS(1,4)`
stability.  A single defect already contains both compression directions,
with exactly equal normalized Hilbert--Schmidt norms.

This reformulation also locates the boundary of the known permanence
theorems.  The relevant edge groups in `(BH6)` are infinite free groups, and
the cyclic edge in the equivalent amalgam description is infinite.  The HNN
edge isomorphism `phi` does not extend to an automorphism of the free vertex
group.  Consequently the finite-edge and identical-subgroup HNN theorems of
Gerasimova--Shchepin do not apply.

## 2. The central skeleton and its index-two core

Work first with the abstract central presentation

```text
S=<z,A,C,X |
    z^2=1, z central,
    A^2=z,
    A^(-1) C A=C^(-1),
    C X C^(-1)=X^4>.                                 (BH7)
```

There is a homomorphism

```text
q:S->C_2,
q(A)=1,       q(z)=q(C)=q(X)=0.                      (BH8)
```

Every relator in `(BH7)` has even `A`-parity, so `(BH8)` is well-defined and
surjective.  Let `J=ker(q)`.  Taking the Schreier transversal `{1,A}` and
putting `Y=A^(-1)XA`, the relations in the two Schreier sheets are

```text
C X C^(-1)=X^4,
C^(-1) Y C=Y^4.                                      (BH9)
```

The second line follows directly from the first:

```text
A^(-1)(C X C^(-1))A
 =(A^(-1)CA)(A^(-1)XA)(A^(-1)C^(-1)A)
 =C^(-1)YC
 =Y^4.                                                (BH10)
```

The central involution `z` occurs in no further relation in the core.  Hence

```text
J ~= J_0 x C_2,                                      (BH11)
```

where `J_0` is the group in `(BH4)`.  Conjugation by `A` acts on the core by

```text
A^(-1) C A=C^(-1),
A^(-1) X A=Y,
A^(-1) Y A=A^(-2) X A^2=X,
A^(-1) z A=z.                                        (BH12)
```

The third identity uses `A^2=z` and centrality of `z`.  Therefore this action
has order two.  The extension `(BH8)` need not split before killing `z`,
because the chosen lift satisfies `A^2=z`.  Modulo `z`, however, `A` is an
involution and `(BH5)` follows.

The modular order-three relators are deliberately absent from `S`.  In fact,
`(A X^2)^3=z` has odd `A`-parity, so the full Iwahori group does not retain
the quotient `(BH8)`.  The index-two decomposition is a tool for the
reflection--BS repair stage, not a new decomposition of
`SL_2(Z[1/2])` itself.

## 3. The free-group HNN description

Let

```text
F=F(X,Y),
H=<X,Y^4> <= F,
K=<X^4,Y> <= F.                                      (BH13)
```

Because `F(X,Y)=<X>*<Y>`, the two displayed generating pairs are free bases
of their respective subgroups.  Thus the assignment

```text
phi:H->K,       X |-> X^4,       Y^4 |-> Y            (BH14)
```

is an isomorphism.  The HNN extension with stable letter `C` and convention
`C h C^(-1)=phi(h)` has defining relations

```text
C X C^(-1)=X^4,
C Y^4 C^(-1)=Y.                                      (BH15)
```

The second line of `(BH15)` is equivalent to
`C^(-1)YC=Y^4`.  This proves `(BH6)`.

The stable-letter exponent gives a surjection

```text
ell:J_0->Z,       ell(C)=1, ell(X)=ell(Y)=0.           (BH16)
```

The reflection satisfies `ell(theta(g))=-ell(g)`.  In this precise sense the
reflection pairs the expanding `X` channel with the counter-oriented `Y`
channel.  It removes the one-sided modular direction from the projective
quotient, even though the index-two core itself still has `(BH16)`.

## 4. Exact equality of the two defects

Let `A,C,X` be unitaries in a finite tracial matrix algebra satisfying the
first two relations of `(BH1)` exactly, and define `Y` by `(BH2)`.  No
approximation is used in the following identity:

```text
C^(-1)YC-Y^4
 =A^(-1)(C X C^(-1)-X^4)A.                           (BH17)
```

Indeed, `(BH17)` is just `(BH10)` before setting the defect equal to zero.
Unitary invariance of normalized Hilbert--Schmidt norm gives

```text
||C^(-1)YC-Y^4||_2
   =||C X C^(-1)-X^4||_2.                            (BH18)
```

Therefore a sequence of reflection-exact triples with vanishing forward
`BS(1,4)` defect is automatically a sequence of almost representations of
the balanced HNN core `(BH4)`, equipped with an exact projective implementer
of `theta`.  There is no second error budget and no independent reverse
repair to prove.

Conversely, suppose an exact equivariant correction of the core supplies
unitaries `C',X',Y',A'` such that

```text
C'X'(C')^(-1)=(X')^4,
(C')^(-1)Y'C'=(Y')^4,
(A')^(-1)C'A'=(C')^(-1),
(A')^(-1)X'A'=Y',
(A')^2=epsilon 1.                                    (BH19)
```

Then `(A',C',X')` is an exact reflection-preserving `BS(1,4)` correction.
The variable `Y'` is forced by equivariance and can be eliminated.  Movement
of `Y` is controlled without a new constant:

```text
||Y'-Y||_2
 <=2||A'-A||_2+||X'-X||_2.                           (BH20)
```

Hence the original correction problem and equivariant repair of `(BH4)` are
quantitatively equivalent, before the two modular order-three constraints
are restored.

## 5. Why the existing HNN permanence theorem does not close the gate

Gerasimova--Shchepin prove Hilbert--Schmidt stability permanence for HNN
extensions over finite subgroups.  They also prove a special conjugator
theorem for an HNN extension in which the two embedded subgroups are
literally identical.  Neither hypothesis holds here.

In the HNN description `(BH6)`, the associated groups `H` and `K` are
infinite free groups.  Moreover, the edge isomorphism `phi` cannot be the
restriction of an automorphism of the base free group `F(X,Y)`.  If an
automorphism `Phi` of `F(X,Y)` extended `phi`, then

```text
Phi(X)=X^4.                                           (BH21)
```

On abelianization, an automorphism of `F_2` induces a matrix in
`GL_2(Z)`, whereas `(BH21)` sends the primitive vector `(1,0)` to
`(4,0)`.  This is impossible.  Thus a base change cannot turn `(BH6)` into
the identical-subgroup HNN covered by the conjugator theorem.

Equivalently, before passing to the index-two core one may write the
projective skeleton as

```text
D_infinity *_(<C>) BS(1,4),                           (BH22)
```

where `<C> ~= Z`.  The general amalgam permanence theorems in the same paper
require a finite edge (with some refinements for finite almost-normal or
finite-normal edges).  The representation group of `Z` has infinitely many
irreducible characters, so the finite-rank restriction-semigroup criterion
used there also does not apply.

The issue is therefore not that the skeleton was overlooked as an HNN
extension.  It is a particular **infinite-edge, non-extendable, equivariant
HNN** problem.

## 6. The sharpened next theorem

The first nonlinear target can now be separated from the modular constraints.

The prime-cycle construction in
`FALSE_ODD_SPECTRAL_EQUIVARIANT_COARSENING.md`, Section 6, already lies in
the exact reflection locus of `(BH17)`: its common squares, factorization,
and reflection relation are exact, and its balanced HNN defect tends to zero.
Nevertheless, every invariant partition of the original prime orbit has
either asymptotically full reflection leakage or a fixed spectral-collapse
cost.  Therefore a proof of the theorem below cannot keep the original orbit
decomposition fixed.  It must permit negligible padding, cutting, or joining
of orbits.  That example does not refute such a flexible repair: it has only
one parity seam, supported on `o(L)` coordinates.  It does show that an
``equivariant coarsening of the given orbit'' is not a valid proof strategy.

> **Balanced-HNN equivariant repair.**  Every normalized-HS almost
> representation of `(BH4)` obtained from an exact projective reflection as
> in `(BH17)` is, after negligible padding, close to an exact representation
> of `(BH4)` carrying a nearby projective implementer of `theta`.

This statement is weaker than unrestricted stability of `J_0`: it only asks
about the `theta`-equivariant locus, and the two HNN defects are tied by the
exact identity `(BH17)`.  It is stronger than ordinary `BS(1,4)` stability,
because the correction must preserve a common reflected stable letter rather
than repair the two orientations independently.

After this theorem, the remaining local task is to perform the equivariant
repair while retaining

```text
(A X^2)^3=epsilon 1,
(A^(-1) C X)^3=epsilon 1.                            (BH23)
```

Those are precisely the modular shared-variable constraints from `(DRB3)`.
The global regular-sector basin theorem remains independent, as explained in
`TRUE_AUTOMORPHIC_GAP_DOES_NOT_CAPTURE_THE_IWAHORI_BASIN.md`.

## 7. Status

The index-two calculation, the HNN presentation, the involution `theta`, the
defect identity `(BH17)--(BH18)`, the movement estimate `(BH20)`, and the
non-extension argument `(BH21)` are exact.

Balanced-HNN equivariant repair is not proved here.  This note reduces the
reflection stage to one symmetric infinite-edge lifting problem and prevents
an invalid appeal to finite-edge or identical-subgroup HNN permanence.  It
does not prove Dogon--Vigdorovich Question 1.4 or the existence of a
nonhyperlinear group.

## References

- M. Gerasimova and K. Shchepin,
  [*Stability of amalgamated free products and HNN extensions*](https://arxiv.org/abs/2305.08720v2),
  especially the identical-subgroup HNN theorem and the finite-edge
  permanence results.
- A. Levit and I. Vigdorovich,
  [*Characters of solvable groups, Hilbert--Schmidt stability and dense
  periodic measures*](https://arxiv.org/abs/2206.02268), for ordinary
  `BS(1,n)` Hilbert--Schmidt stability.
- A. Dogon and I. Vigdorovich,
  [*Hyperlinearity, stability and asymptotic spectral gap of higher rank
  lattices*](https://arxiv.org/abs/2506.20843v2), Question 1.4.
