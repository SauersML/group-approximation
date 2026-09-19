---
rg: 2
id: single-lamps-recover-set-action-proof
kind: route
title: Read the set labels off the single-coordinate lamps
target: single-lamps-recover-set-action
requires: []
artifacts:
  - notes/NOTEPAD.md
---

# Read the set labels off the single-coordinate lamps

Internal proof, transcribed from `notes/NOTEPAD.md` (section "The 2026
sofic-action permanence theorem cannot make the Kun--Thom lamp hyperlinear",
Lemma "single lamps recover the set action").  `requires: []` is a proof
commitment: the argument below is complete as it stands.

## Statement

Let `G` act on a set `X`, put `D = directSum_X C_2` with `G` permuting
coordinates.  If the automorphism action `G action D` is a sofic `C`-action in
the sense of Alekseev--Bradford Definition 4.23, for any class `C` of groups
whatsoever, then `G action X` is a sofic action on a set.

## Proof, verbatim from the corpus

> Fix finite `F subset G`, `Z subset X`, and `epsilon>0`.  In the
> automorphic-approximation definition take `E subset D` to contain the
> identity and every single-coordinate lamp `delta_z`, `z in Z` (and enlarge
> it by the finitely many products required for partial-homomorphism closure).
> Obtain a finite state set `A`, a good subset `S`, a group `Lambda in C`, and
> injective partial homomorphisms
>
> `pi_s:E->Lambda`,  `s in S`.
>
> Although `Lambda` need not be finite, the union
>
> `B=union_(s in S) pi_s({delta_z:z in Z})`
>
> is finite.  Define the set label
>
> `j_s(z)=pi_s(delta_z) in B`.
>
> Injectivity of `pi_s` makes `j_s:Z->B` injective.  Since the automorphism of
> `D` induced by `g` sends `delta_z` to `delta_(gz)`, the covariance equation
> of Definition 4.23 is exactly the orbit-approximation equation for the maps
> `j_s`.  The same approximately multiplicative permutation map on `A`
> witnesses soficity of `G action X`.  End proof.

## Why the target class drops out

The three steps that carry the argument are: finiteness of `B` (a finite union
of images of a finite set), injectivity of `j_s` (inherited from injectivity of
the partial homomorphisms, which is part of the definition), and the identity
`g · delta_z = delta_(gz)` (a property of the permutation action on `D`, not of
`Lambda`).  None mentions `C`.  `Lambda` is used only as a set in which the
finitely many labels `pi_s(delta_z)` live, which is why the conclusion holds
for an arbitrary class and why no enrichment of the targets helps.

The permutation approximation `phi : G -> Sym(A)` is not modified at all: the
same map witnesses the set action.  So there is no loss in the multiplicativity
or orbit-approximation parameters, and the implication is uniform in
`(F, Z, epsilon)`.

## Consequence recorded in the corpus

> Kun--Thom prove that the coset action of their Kazhdan infranormal pair on
> `G/Gamma` is not sofic.  Hence the induced action on its `C_2` lamp group is
> not a sofic hyperlinear action, and the 2026 semidirect-product permanence
> theorem is inapplicable.  This closes the tempting direct route to proving
> the already-nonsofic Kun--Thom wreath product hyperlinear.

## Definitional dependency, stated openly

The statement is *about* Alekseev--Bradford's Definition 4.23, so it inherits
that definition's exact content.  What this repository has read verbatim in the
primary source is their Corollary 5.2 and Theorem 4.18, transcribed in
`research/artifacts/kun-thom-2608-06222-verified.md`; the numbered definition
itself is quoted here at second hand from `notes/NOTEPAD.md`, which describes it
as an automorphic-approximation condition supplying a finite state set, a good
subset, a target group in `C`, and injective partial homomorphisms satisfying a
covariance equation.  The proof above uses exactly those four data and nothing
else, so it is robust to renumbering, but a reader checking the primary source
should confirm the definition number.
