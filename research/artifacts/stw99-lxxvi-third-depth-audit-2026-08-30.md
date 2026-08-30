# STW LXXVI third-depth audit: the two compact-collapse corridors

## Correction at the trust boundary

Equality of Cuntz classes of projections is not, in an arbitrary infinite
C*-algebra, the same as Murray--von Neumann equivalence.  The local-K0
protection argument from the second-depth audit is therefore valid when the
generated ideal after tensoring with Z is stably finite (and in particular
for the Toeplitz compact ideal), but not without a finiteness hypothesis.

This correction splits the compact attack into two corridors.

## Finite corridor

For `J=Ideal(p,q)` with `J tensor Z` stably finite, a Cu collapse forces
Murray--von Neumann equivalence in `J tensor Z`.  Since
`J -> J tensor Z` is a KK-equivalence, `[p]=[q]` already in `K_0(J)`.

If `A` has stable weak cancellation, that local equality already forces
`p~q` before tensoring.  Thus stable weak cancellation together with stable
finiteness of `A tensor Z` makes the first-factor Cu map injective on
projection classes.  Conversely, the exact finite counterexample target is:

```text
A pure,
[p]=[q] in K_0(J) but [p]!=[q] in Cu(A),
stable_rank(J tensor Z)=1.
```

Stable rank one only for `J tensor Z` suffices to collapse the pair.  This is
strictly sharper than assuming cancellation for every projection over
`A tensor Z`.

## Infinite corridor

If `J tensor Z` is not stably finite, equality of the two Cu classes may arise
because their images become infinite.  It need not imply equality in local
K0, so KK-equivalence does not obstruct it.  An example must be non-simple at
the relevant ideal level: simple pure algebras are already Cu-regular, while
the Toeplitz boundary pair remains inside a stably finite compact ideal.

No example in either corridor is constructed.  The finite target is now a
stable-weak-cancellation defect repaired locally to stable rank one by Z; the
infinite target is a genuine change of finiteness/comparison under Z.

## Explicit unstable-clutching construction target

The classical nonzero class `alpha in pi_5(U(2))=Z/2` defines a nontrivial
rank-two complex vector bundle over `S^6` that is stably trivial, since its
image in the stable group `pi_5(U)=Z` is zero.  For a unital coefficient
algebra `D`, scalar extension sends the clutching class through

```text
pi_5(U(2)) -> pi_5(U(M_2(D)))
             -> pi_5(U(M_2(D tensor Z))).
```

If the first image is nonzero, the second is zero, and
`C(S^6) tensor D` is pure, the nontrivial and trivial rank-two bundles give
the exact ideal-local collapse pair.  They are full, have equal K0 class, are
inequivalent before Z, and equivalent afterward.

`D=C` fails purity.  `D=Z` removes the before/after distinction.  The natural
test `D=C*_r(F_2)` is simple pure and non-Z-stable, but neither purity of the
continuous field nor the two unstable unitary-homotopy maps is presently
computed.  The 2026 selfless-correspondence tensor theorem does not apply to
the commutative base as a selfless factor, so this remains an honest two-input
frontier rather than a claimed construction.

## Product lane

The nonseparable product `prod_n Z` still supplies neither target.  Its
coordinate projections are finite, and proving purity or a Cu collapse needs
uniform stabilization and compact-containment witnesses.  Coordinatewise
central Z embeddings work uniformly on each prescribed finite set, so mere
failure of minimal tensor product to commute with products is not evidence of
Cu nonregularity.
