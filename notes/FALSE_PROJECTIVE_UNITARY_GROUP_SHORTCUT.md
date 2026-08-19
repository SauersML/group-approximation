# The projective-unitary-group shortcut stops at trace selection

Date: 2026-08-14

## 1. The tempting argument

Let `M` be a separable non-Connes-embeddable `II_1` factor. Its projective
unitary group

```text
PU(M)=U(M)/T                                             (PUG1)
```

remembers a remarkable amount of the algebra. Dye's reconstruction theorem
and its descendants recover the Jordan structure of suitable von Neumann
algebras from sufficiently strong maps of their projection or unitary
structures. Dowerk--Thom prove that `PU(M)` has bounded normal generation and
that every homomorphism

```text
PU(M) -> K                                               (PUG2)
```

to a **Polish SIN group** is continuous.

This suggests a shortcut: if `PU(M)` were hyperlinear, embed it in a tracial
matrix ultraproduct, use automatic continuity and unitary-group
reconstruction, and conclude that `M` is Connes embeddable.

The conclusion would be spectacular, but the implication is not valid with
the presently available theorems.

## 2. What is genuinely gained: cardinality disappears

Hyperlinearity is local. Therefore

```text
some group is nonhyperlinear
  iff
some finitely generated group is nonhyperlinear.         (PUG3)
```

The forward implication applies even when the original group is uncountable:
if every finitely generated subgroup were hyperlinear, every finite test set
would have a hyperlinear model inside the subgroup it generates.

Consequently, a proof that the **abstract discrete group** `PU(M)` is
nonhyperlinear would already settle existence of a finitely generated
nonhyperlinear group. No prior choice of a countable dense subgroup is
needed. This reduction is formalized as

```text
exists_not_isHyperlinear_iff_exists_fg
```

in `GroupApproximation/Sofic/HyperlinearReduction.lean`.

## 3. Why automatic continuity does not apply

A normalized Hilbert--Schmidt matrix ultraproduct is a complete SIN metric
group, but in general it is nonseparable. It is therefore not a Polish SIN
target. Dowerk--Thom's automatic-continuity theorem does not apply to an
arbitrary hyperlinear embedding

```text
PU(M)_discrete -> product_omega U(d_n).                  (PUG4)
```

Restricting `(PUG4)` to a countable dense subgroup does put the image in a
separable closed subgroup of the target, but it also changes the domain. The
automatic-continuity theorem is a theorem about homomorphisms defined on all
of `PU(M)`, with its Polish topology. It supplies no continuity for an
abstract homomorphism defined only on a countable dense subgroup.

Bounded normal generation does not repair this by itself. Pulling the target
metric back along a homomorphism gives an invariant length `L`. If a
nontrivial `v` normally generates the whole group in at most `f(v)` factors,
then

```text
diam(image) <= f(v) L(v).                                (PUG5)
```

This is a lower bound on `L(v)`, not the upper bound near the identity needed
for continuity. The separability/Baire input in invariant automatic
continuity is essential.

## 4. Why Dye reconstruction does not apply

Dye-type theorems start from an orthoisomorphism of projection lattices, or
from an isomorphism of full unitary groups with enough preservation and
surjectivity to recover that lattice. A raw injective group homomorphism into
the unitary group of a larger finite algebra supplies neither.

Projective involutions do encode symmetries `1-2p`, but a monomorphism only
preserves group equations among those symmetries. It does not automatically
preserve orthogonality, arbitrary suprema, trace, or the assertion that the
image is the full unitary group of a von Neumann subalgebra. Those are exactly
the hypotheses used by projection-lattice reconstruction.

Finite-dimensional calibration already warns against the missing step:
compact projective unitary groups have many faithful continuous unitary
representations besides the defining one. A faithful group representation
does not determine the defining matrix trace.

## 5. The decisive trace mismatch

Hyperlinearity of a discrete group `G` asks for approximation of its **regular
character**

```text
delta_e(g)=1 if g=e, and 0 otherwise.                    (PUG6)
```

The inclusion of `U(M)` in `M` carries instead the natural character

```text
u |-> tau_M(u).                                         (PUG7)
```

The GNS algebra of `(PUG7)` can recover `M`, but a hyperlinear embedding of
the abstract discrete group approximates `(PUG6)`, not `(PUG7)`. There is no
general trace-selection theorem converting one into the other. Connes
embeddability is not inherited by arbitrary finite-factor representations of
a hyperlinear group; asserting that would already bridge the central gap.

This is the same boundary encountered in the IRS and full-group routes: group
relations can provide a desired representation, while hyperlinearity singles
out the regular representation.

There is a sharp algebraic calibration. Every group is a quotient of the free
group on its underlying set, and free groups are hyperlinear. Hence

```text
every group is hyperlinear
  iff
hyperlinear groups are closed under arbitrary quotients. (PUG8)
```

Equivalently, a nonhyperlinear group exists iff some hyperlinear free group
has a nonhyperlinear quotient. Thus using the natural finite-factor
representation as though Connes embeddability passed to its quotient is not a
minor permanence lemma; unrestricted quotient permanence is the entire
universal-hyperlinearity problem. Both forms are formalized source-first as
`all_groups_isHyperlinear_iff_quotient_closed` and
`exists_not_isHyperlinear_iff_exists_hyperlinear_quotient`.

## 6. Exact live endpoint

The route becomes valid if one proves either of the following genuinely new
statements.

1. **Discrete unitary rigidity.** For a non-CE factor `M`, the abstract group
   `PU(M)` is not hyperlinear.
2. **Regular-to-natural trace selection.** Hyperlinearity of `PU(M)` forces a
   matrix approximation of a finite-type character whose GNS algebra contains
   `M` trace-preservingly.

Either statement, combined with `(PUG3)`, produces a finitely generated
nonhyperlinear group. Existing automatic-continuity and Dye reconstruction
theorems do not prove either statement.

## References

- P. A. Dowerk and A. Thom, *Bounded Normal Generation and Invariant
  Automatic Continuity*, arXiv:1506.08549, especially Theorems 1.3 and 1.4.
- J. Hamhalter, *Dye's Theorem and Gleason's Theorem for AW*-algebras*,
  arXiv:1408.4597, especially the projection-lattice hypotheses in the main
  theorem.
