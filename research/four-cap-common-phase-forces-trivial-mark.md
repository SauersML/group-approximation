---
rg: 2
id: four-cap-common-phase-forces-trivial-mark
kind: claim
title: A cap-independent OR3 Fourier phase forces the central sign trivial
distinct_from:
  edgeful-or3-four-cap-walsh-packet: that claim constructs and classifies the four separate finite Fourier cap blocks; this claim computes their Hecke gauge equations and proves that identifying the cap restrictions globally destroys the marked packet.
  central-hecke-controlled-multipaths-remain-sectorwise: that claim proves that central controls split every word sectorwise; this claim identifies the exact collapse that occurs when those controls are removed from the four-cap OR3 packet.
  packet-retraction-evaluates-hecke-collision-atlas: that obstruction uses a packet retraction to obtain a finite evaluation; the collapse here is an exact algebraic consequence and assumes neither a retraction nor finite dimensionality.
---

**ESTABLISHED.**  In the Morita coordinates of
`primitive-packet-corner-is-matrix-over-hecke-atom`, let

```text
H=e C[Gamma] e
```

be the rank-one Hecke atom.  On the Fourier block of the affine OR3 cap
`H_l=t_l+V_l`, choose unitaries `h_(l,chi) in U(H)` and put

```text
phi_(l,j)=e_j|V_l,
u_(l,j)(chi)=h_(l,chi+phi_(l,j)) h_(l,chi)^*.            (FCP1)
```

Then the phase-wordized logical marginal is

```text
S_(l,j)=(-1)^((t_l)_j)
        sum_(chi in V_l^*)
        u_(l,j)(chi) E_(chi+phi_(l,j),chi).              (FCP2)
```

The coefficient holonomy is exactly flat:

```text
u_(l,j)(chi+phi_(l,j))=u_(l,j)(chi)^*,                  (FCP3)

u_(l,k)(chi+phi_(l,j)) u_(l,j)(chi)
 =u_(l,j)(chi+phi_(l,k)) u_(l,k)(chi).                 (FCP4)
```

There is no further free cap-block holonomy in this diagonal-gauge ansatz:
every coefficient in `(FCP1)` is a coboundary, and `(FCP4)` is its square
flatness identity.

The four cap parities are

```text
l=110: S_a S_b=J,
l=101: S_a S_c=J,
l=011: S_b S_c=J,
l=111: S_a S_b S_c=J,                                  (FCP5)
```

where `J` is the common central sign and each marginal is an involution.
These identities hold blockwise before and after the Hecke gauge
conjugation.

Consequently a **cap-independent** common-word coupling is impossible in a
marked model.  More precisely, in any unital algebra, if central `J` and
involutions `A,B,C` satisfy the first three equations obtained by replacing
all cap restrictions in `(FCP5)` by the same `A,B,C`, then

```text
AB=J and AC=J  imply B=C,
BC=J and B=C   imply J=B^2=1.                           (FCP6)
```

If the `111` equation `ABC=J` is imposed as well, then `J=1` and the first
three equations give `A=B=C`, while `ABC=1` gives `A=B=C=1`.  Thus a single
literal coefficient word shared across all four caps does not produce a
nonretractive block-escaping atlas: it kills the central mark (and with all
four parities, the common marginals) in **every** representation, including
the intended infinite algebraic one.

There is only one algebraic escape from `(FCP6)`: retain mutually orthogonal
cap selectors `q_l` and impose `(FCP5)` after compression by `q_l`.  Then the
products from different lines of `(FCP5)` cannot be multiplied together,
so the collapse does not follow.  But a word

```text
A=sum_l q_l A_l
```

is precisely a centrally controlled multipath.  If the `q_l` are central
relative to the generated words, every relation decomposes sectorwise and
has no cross-cap holonomy.  Therefore the four-cap packet leaves the same
sharp gate as the general controlled-multipath theorem: a viable coupling
must authenticate a selector that is noncentral relative to another chart,
or otherwise mix two cap sectors inside one collision block.  Merely using
one common cap-independent word universally destroys packet injectivity;
merely using central cap-dependent words creates no interference.
