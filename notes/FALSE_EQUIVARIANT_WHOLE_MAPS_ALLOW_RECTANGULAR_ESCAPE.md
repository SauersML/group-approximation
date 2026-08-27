# Equivariant whole maps still allow the rectangular Leavitt escape

Date: 2026-08-14

## 1. Outcome

`TRUE_EQUIVARIANT_TRANSITIONS_COARSEN_TO_WHOLE_MAPS.md` closes the passage
from equivariant transition PVMs to classical whole response maps.  It does
**not** yet put the source and target labels in the same finite paired
quotient.  That distinction is load-bearing.

There is an exact finite model in which all four Leavitt transports are
deterministic equivariant maps, the two diagonal pairing identities and both
cross-zero identities hold exactly, but the target paired spaces have twice
the vector-space dimension of the source.  The robust `1/36` self-map floor
does not apply.

At the matrix level the larger target alphabet is paid for by smaller target
multiplicities.  Source and target representations can therefore occupy the
same total matrix dimension.  Unitary compressor covariance and exact
whole-map extraction do not remove this rectangular escape.

The remaining gate is consequently:

```text
equivariant whole maps
 + same-orbit / same-paired-quotient closure
 -> robust 1/36 contradiction.                       (RWE1)
```

The second line, not equivariance, is the genuinely matrix-specific
finite-multiplicity theorem.

## 2. Exact rectangular pairing model

Let `V,W` be nonzero finite binary vector spaces with a perfect pairing

```text
b:V x W -> F_2.                                      (RWE2)
```

Put

```text
V'=V directSum V,
W'=W directSum W,                                    (RWE3)
```

and give them the orthogonal-sum perfect pairing

```text
b'((v0,v1),(w0,w1))=b(v0,w0)+b(v1,w1).              (RWE4)
```

Define the four linear embeddings

```text
R0(v)=(v,0),            R1(v)=(0,v),
L0(w)=(w,0),            L1(w)=(0,w).                (RWE5)
```

Then for every `v,w`,

```text
b'(R0(v),L0(w))=b(v,w),
b'(R1(v),L1(w))=b(v,w),
b'(R0(v),L1(w))=0,
b'(R1(v),L0(w))=0.                                  (RWE6)
```

Thus the complete binary Leavitt pairing table is realized with zero error
by deterministic maps.  There is no conflict with
`RobustPairedQuotientFloor.lean`, because that theorem assumes

```text
R_i:V->V,                L_j:W->W,                   (RWE7)
```

whereas `(RWE5)` has larger codomains.  Indeed

```text
|V'|=|V|^2,             |W'|=|W|^2.                 (RWE8)
```

This is the finite linear shadow of the properly infinite Leavitt module:
two orthogonal child copies fit in a larger parent coordinate system.

## 3. Full translation equivariance is present

Regard `V` and `V'` as translation torsors over themselves.  Each `R_i` is
equivariant for the homomorphism `R_i:V->V'`:

```text
R_i(v+x)=R_i(v)+R_i(x).                              (RWE9)
```

The same holds for `L_j`.  Consequently `(RWE5)` already satisfies the
strongest exact hypothesis of the equivariant whole-map theorem.  Every map
is a single classical whole response map; no contextuality, no-signaling
box, commutant gauge, or PVM incompatibility remains.

Equivariance therefore cannot prove that the output orbit equals the input
orbit.  It only proves that the output is one orbit for the image translation
group.  A proper translation-group embedding is exactly what `(RWE5)` uses.

## 4. Equal ambient matrix dimension does not help

Let `N=|V|=|W|`.  The irreducible finite Weyl representation attached to
`b` has dimension `N`.  The representation attached to the direct-sum
pairing `b'` has dimension `N^2`.  Put the source representation on

```text
C^N tensor C^N                                      (RWE10)
```

as the first Weyl factor tensored with an `N`-dimensional multiplicity, and
put the target direct-sum Weyl representation irreducibly on the same
`N^2`-dimensional space.  A unitary identifies the two underlying Hilbert
spaces.

Under this identification:

* source character atoms have rank `N`;
* target fine atoms have rank one;
* every source atom is the sum of `N` target extension atoms; and
* a latent affine section selects one rank-one target atom over every source
  atom.

This is exactly the multiplicity-splitting geometry of a proper compressor.
Total matrix dimension and normalized trace are perfectly balanced.  The
finite-dimensional equality of source and target Hilbert dimensions does
not imply equality of their paired label dimensions.

## 5. Iterated escape

The construction iterates.  At depth `n`, use

```text
V_n=directSum_(words of length n) V,
W_n=directSum_(words of length n) W.                 (RWE11)
```

Each binary branch embeds level `n` into one half of level `n+1`, and the
orthogonal-sum pairing realizes every diagonal/crossed table exactly.  By
increasing the source multiplicity at level `n`, consecutive Weyl systems
again fit in the same ambient matrix dimension.

Thus growing windows, exact finite-depth functoriality, and equivariant
whole-map recovery can all coexist with a fresh rectangular direction at
every depth.  This is the paired-translation version of the Bernoulli
extension-fiber countermodel.

## 6. Corrected live theorem

The whole-map result remains useful: it removes the common-classical-law
gate.  What remains is now sharply separated from it.

> **Same-orbit paired-translation closure.**  In a hypothetical matrix
> microstate of the actual rank-five Leavitt group, show that on a
> positive-density sum of negative long-root sectors, the two child
> translation images produced by `a |-> a t_i` and `b |-> s_j b` act inside
> one source-sized recovered paired translation orbit, up to vanishing
> normalized boundary leakage.

Equivalently, rule out the coordinatewise multiplicity conversion

```text
source Weyl factor tensor growing multiplicity
       -> larger target Weyl factor tensor smaller multiplicity. (RWE12)
```

Abstract finite-von-Neumann-algebra arguments cannot prove this: the regular
representation realizes the infinite version.  The proof must use a
matrix-coordinate/Connes-embeddability property, such as compatible
commutant recovery or a carrier-coupled finite-multiplicity identity.

Once same-orbit closure is available, the equivariant orbit construction
gives a common law of self-maps, and the existing `1/36` theorem finishes
without another analytic step.

No local computation or build was run for this note.
