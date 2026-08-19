# `SL2F13` radical application: useful theorem and extension-orientation correction

Date: 2026-08-13

## Provenance

The external arithmetic certificate discussed here is the repository

[`eekarabiyik/SL2F13`](https://github.com/eekarabiyik/SL2F13/tree/main).

That repository, not the present project, supplies the exact degree-14
polynomial and the Sage/GAP verification identifying its splitting-field
Galois group with `PSL(2,13)`.  In particular, its
[`anc/code/group_certificate.g`](https://github.com/eekarabiyik/SL2F13/blob/main/anc/code/group_certificate.g)
checks all of the finite-group facts used below:

* the degree-14 transitive group is isomorphic to `PSL(2,13)` and has order
  `1092`;
* every involution has cycle shape `1^2 2^6` in that action;
* the pullback of the Schur double cover of `A_14` has order `2184`, is
  perfect, and is isomorphic to `SL(2,13)`; and
* an involution in `PSL(2,13)` lifts to an element of order four.

Those are credited computations.  This note records only consequences of
combining them with the MF-radical theorem of the present repository.

## 1. Correction: the displayed witness extension does not by itself prove soficity

The Clifford witness has a split exact sequence

```text
1 -> ClLamp(X) -> W -> V -> 1,
```

where `ClLamp(X)` is locally finite and hence amenable, while the relevant
linear quotient is residually finite and hence sofic.  It is tempting to
conclude that `W` is sofic by extension permanence.  That inference reverses
the known theorem.

Elek--Szabo prove the permanence direction

```text
sofic normal subgroup + amenable quotient => sofic total group.
```

The displayed sequence for `W` has an amenable normal subgroup and a sofic
quotient.  General `amenable-by-sofic` permanence is not available.  The
post-2026 nonsofic generalized-wreath-product constructions make this
orientation especially load-bearing.  Therefore the short exact sequence
alone must not be cited as a proof that `W` is sofic.

The conclusion that a finitely generated sofic non-MF group exists is still
valid by the different finite-tower construction in
`TRUE_LITERAL_NONMF_MARK_IS_CE_VISIBLE.md`.  There each finite Clifford stage
is a **split finite extension** of the residually finite base, the directed
union is sofic, the automorphic direct limit is sofic, and the final quotient
is `Z`, which is amenable.  The image of the literal group in that sofic
target retains the MF-radical mark.  Thus the valid conclusion is

```text
there exists an explicit finitely generated sofic non-MF group,
```

but the proof must use that tower, not the bare extension theorem.

There is a further specific repair.  The automorphic dilation of the tower
has site set equivariantly isomorphic to `V/Gamma`: if `x_0` is the root of
`Gamma/beta(Gamma)` and `y=T^(-1)x_0`, the dilation group `V` acts
transitively on the site set and `Stab_V(y)=Gamma`.  Thus the final tower
group is canonically

```text
ClLamp(V/Gamma) semidirect V = W.
```

This proves that the original witness `W` **is** sofic, but for the special
finite-tower reason, not from general amenable-by-sofic permanence.  The
detailed level/stabilizer calculation is recorded in
`TRUE_LITERAL_NONMF_MARK_IS_CE_VISIBLE.md`.  Consequently the strongest
structural statement survives the audit:

```text
W is finitely generated, locally-finite-by-residually-finite,
sofic, and non-MF.
```

## 2. General radical implantation theorem

Let `E` be the literal non-MF group and let

```text
1 != w in Rad_MF(E),   w^2 = 1.
```

Let `A` be any group with an involution `a` whose normal closure is all of
`A`.  Form

```text
H_A = E *_(<w>=<a>) A.
```

Bass--Serre normal form embeds both vertex factors.  In particular the
canonical image of `a=w` is nontrivial.  MF-radical functoriality puts that
image in `Rad_MF(H_A)`.  Since the radical is normal, it contains the normal
closure of `a` inside the embedded copy of `A`; hence

```text
A <= Rad_MF(H_A).
```

Consequently every homomorphism from `H_A` to an MF group kills the entire
embedded copy of `A`.  If `A` is finitely presented, then `H_A` is finitely
presented as well.  The formal radical core is the theorem

```text
normMFResidual_eq_top_of_image_normalClosure_eq_top
```

in `Sofic/NormallyGeneratedMFObstruction.lean`.  The Lean theorem is stated
for an arbitrary homomorphism; the amalgam normal-form injection is the
separate Bass--Serre input.

## 3. Arithmetic specialization

Take

```text
A = PSL(2,13).
```

This nonabelian finite simple group contains involutions, and every nontrivial
element normally generates it.  Identifying `w` with any involution `a` gives
a finitely presented amalgam `H_13` with

```text
PSL(2,13) <= Rad_MF(H_13).
```

Via the credited `SL2F13` certificate, this implanted finite simple subgroup
may additionally be described as the Galois group of the certified totally
real degree-14 polynomial.  The inverse-Galois description is an arithmetic
realization of the implanted group; it is not needed for the radical proof.

## 4. The spin cover is a consistency check, not a finite witness

The credited certificate identifies the nonsplit central cover

```text
1 -> {+-I} -> SL(2,13) -> PSL(2,13) -> 1
```

and checks that projective involutions lift to order four.  This is a useful
finite analogue of the Clifford central sign.  It cannot, however, provide a
homomorphism `E -> SL(2,13)` sending `w` to `-I`: the exact
finite-dimensional kill theorem for `E` sends `w` to the identity in every
finite-dimensional linear representation over every field.  Any proposed
finite-group detector of the original marked word is therefore automatically
inconsistent with the proved theorem.

## 5. Relevance to the hyperlinear problem

The implantation theorem enriches the operator-norm MF radical and gives a
concrete inverse-Galois application.  It does not put an element in the sofic
radical, and it does not construct a Connes-embeddable representation that
retains such an element.  Therefore it does not close the current
hyperlinear-versus-sofic gate.  It belongs as a credited application note,
not as evidence that the remaining tracial implication has been proved.
