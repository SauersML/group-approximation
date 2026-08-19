# A finite extension synchronizes Leavitt star on the raw coefficient cut

Date: 2026-08-13

## 1. The inverse-transpose extension

Let `Q` be the binary Leavitt atlas group and let `theta` be the transpose
anti-involution of the coefficient algebra, combined with matrix transpose.
On group units the formula

\[
 \psi(g)=\theta(g^{-1})
 \tag{RSSync1}
\]

is multiplicative.  Since `theta` is involutive, so is `psi`.  Form the
concrete semidirect extension

\[
 Q^\sharp=Q\rtimes_\psi C_2
 =\langle Q,j\mid j^2=1,\ jgj=\psi(g)\rangle.
 \tag{RSSync2}
\]

This is not being asserted nonhyperlinear here.  It is an explicit modified
candidate with one additional involution.  It remains nonsofic: if
`Q^sharp` were sofic, its subgroup `Q` would be sofic.

In every unitary representation of `Q^sharp`, `(RSSync2)` gives the exact
twisted-adjoint identity

\[
 \pi(\theta(g))=J\pi(g)^*J,
 \qquad J=\pi(j).
 \tag{RSSync3}
\]

Thus the extension supplies the spatial operation which the false
identification `q^star=q^-1` was missing.

## 2. Compatibility with the raw cut

The scalarized raw involution is fixed by Leavitt transpose.  Its prefix
table contains the two opposite terms `001 11*` and `11 001*`, while every
other term is self-adjoint.  Exact all-depth arithmetic verifies

\[
 \theta(r)=r.
 \tag{RSSync4}
\]

Since `r=r^-1`, `(RSSync1)` also fixes `r`, so

\[
 [j,r]=1.
 \tag{RSSync5}
\]

The trace-half coefficient projection

\[
 \widehat e=(1-\widehat r)/2
\]

from `TRUE_RAW_PAULI_COEFFICIENT_CUT.md` is therefore preserved by the
spatial star implementer.  The two equal coefficient halves are not mixed
by `J`.

## 3. The synchronized finite chart

On the compressed scalar subgroup

\[
 H=GL_3(2),
\]

the automorphism in `(RSSync1)` is

\[
 g\longmapsto(g^{-1})^{\mathsf T}.
 \tag{RSSync6}
\]

An exhaustive exact audit of all `168` matrices verifies that `(RSSync6)`
is an involutive outer automorphism.  Hence

\[
 |H\rtimes_\psi C_2|=336.
 \tag{RSSync7}
\]

Because `r` centralizes the entire compressed core and is fixed by `j`, the
finite subgroup obtained after adjoining the raw sign has order

\[
 |(H\rtimes_\psi C_2)\times\langle r\rangle|=672.
 \tag{RSSync8}
\]

This subgroup can be exactified at every matrix coordinate.  Consequently
the transpose/adjoint synchronization and the trace-half raw coefficient
cut coexist in one fixed finite representation packet; their compatibility
does not require lifting an infinite-group commutant.

## 4. Precise gain and remaining gate

The extension closes the **adjoint gate** for root-character extraction.
For elementary roots, inverse-transpose exchanges the opposite roots and
applies Leavitt star to the coefficient.  Equation `(RSSync3)` therefore
turns the opposite-root Fourier block into the genuine Hilbert-space
adjoint of the original block, up to the fixed spatial involution `J` which
preserves `hat e`.

It does not by itself turn characteristic-two addition into complex
addition.  That operation must still pass through multiplication in a
finite elementary-abelian root subgroup, and coefficient multiplication
must still pass through Steinberg commutators.  The remaining target is now:

> In the joint finite `672`-element chart sector, use the paired opposite
> root Fourier blocks and the `J` symmetry to extract the comb coefficient
> operator on `hat e`; prove the forbidden leakage block vanishes while its
> adjoint-side companion retains fixed mass.

This is strictly narrower than the previous unsynchronized projection
recovery problem: the carrier, its trace, its finite coefficient placement,
and the correct adjoint operation are all fixed.

The two-sheet operation also cannot create the required directionality.
`FALSE_STAR_SYNCHRONIZATION_DOES_NOT_CREATE_LEAKAGE.md` proves that forward
and reverse leakage of every diagonal doubled transport are exactly the
averages of the corresponding sheet leakages.  Since `theta(r)=r`, the
sheet swap commutes with the doubled raw cut.  Thus star synchronization
solves adjoint compatibility only; a cross-root multiplication relation is
still indispensable for restricting the multiplicity holonomy.

## 5. Replay

The exact audit is

```text
experiments/atlas_raw_star_extension.py
```

with output

```text
experiments/atlas-raw-star-extension.json
```

It enumerates `GL_3(2)`, checks the automorphism and absence of an inner
implementer, records the order distribution of the order-336 semidirect
product, and independently verifies `theta(r)=r` by exact Leavitt prefix
arithmetic.
