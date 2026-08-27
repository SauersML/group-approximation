---
rg: 2
id: signed-character-operator-decoding-proof
kind: route
title: Make derivatives constant and diagonalize their signed Koopman sectors
target: signed-character-expansion-decodes-operator-parallelograms
requires: []
---

Argue by contradiction.  Take a sequence with square energy tending to zero
but distance from every table `(SCE5)` bounded below, and pass to the tracial
metric ultraproduct together with the Loeb counting spaces of the `G_i`.
Write `Q(g)` for the limiting reflection field.

For `a in A`, form the left derivative

```text
D_a(g)=Q(ag)Q(g).                                           (SCD1)
```

On a face `[a,g,b]`, jointness makes every entry commute and parity gives

```text
D_a(gb)=D_a(g).                                             (SCD2)
```

The uniform right spectral gap, applied after tensoring its scalar Markov
operator with the Hilbert space `L_2(M)`, says that `(SCD2)` makes `D_a(g)`
independent of `g`; call its value `P_a`.  The edge commutator on
`Q(g),Q(ag)` shows that `P_a` is a reflection and commutes with `Q(g)` for
almost every `g`.  Hence all the `P_a` commute with one another, and

```text
Q(ag)=P_a Q(g).                                             (SCD3)
```

Let `z_sigma` be the joint spectral projections of the bounded commuting
tuple `(P_a)_(a in A)`.  On the `sigma` sector, `(SCD3)` reads

```text
Q(ag)z_sigma=sigma(a)Q(g)z_sigma.                           (SCD4)
```

Apply the coefficient-Hilbert-space version of `(SCE2)`.  If `sigma` is not
a character, `(SCD4)` forces `z_sigma=0`, since `Q(g)` is unitary.  If it is
the restriction of `chi`, the kernel description in `(SCE2)` gives one
constant coefficient `S_sigma` with

```text
Q(g)z_sigma=chi(g)S_sigma.                                  (SCD5)
```

The coefficient is a reflection in the corner `z_sigma M z_sigma`.
Splitting it into its two spectral projections produces the extra affine
constant `c` in `(SCE5)`.  Different `sigma` corners are orthogonal, so the
resulting family is one commuting affine PVM and equals `Q` in the limit,
contradicting the assumed distance floor.  This compactness contradiction
gives a dimension- and size-independent modulus in `(SCE4)`.

All uses of expansion are Hilbertian tensor extensions of scalar spectral
inequalities.  No spectral disintegration over a growing hyperfinite family
is used: the only internal spectral split is the fixed finite tuple
`(P_a)`, with at most `2^|A|` projections.
