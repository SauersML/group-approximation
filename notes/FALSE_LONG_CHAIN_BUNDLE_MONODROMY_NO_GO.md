# Monodromy obstructs the naive long-chain principal-bundle splice

Date: 2026-08-11

## 1. Outcome

The long paired Fourier chain and the exact principal-bundle prescription
cannot be combined by the most direct coinduced construction.  The second
compressor accumulates one coefficient shear after every complete depth
cycle.  If the coefficient shear has order `r`, then the projective order
of the second compressor is divisible by `M r`, whereas the common-positive
arc has length only `M`.

Consequently, on an exact finite transvection orbit, the two coinduced
positive models agree on at most a fraction `1/r` of the blocks.  For the
primitive `p^n`-torsion clock used in the radical construction,

`r=p^(n-1)`.                                             `(LCM1)`

The squared normalized Hilbert--Schmidt discrepancy of a primitive
positive translation in the direct-sum bundle is therefore at least

`2(1-p^(-(n-1)))`.                                      `(LCM2)`

It does not tend to zero when the chain length tends to infinity.

This does not invalidate either component theorem:

1. the long chain gives exact agreement before its first wrap and an
   undiluted inverse fold; and
2. the principal-bundle theorem gives an exact external representation
   with either compressor prescribed.

It rules out only their naive coinduced splice, in which the fiber over a
transvection orbit is obtained by successively conjugating one common
positive representation by the prescribed compressor.  A successful
globalization must cancel the accumulated shear between different chains
or use a genuinely nonconstant fiber functor.  Merely increasing `M` cannot
solve the simultaneous-coherence problem.

## 2. Abstract cyclic calculation

Use the notation of `FALSE_LONG_FROBENIUS_ELEMENTARY_COMPRESSOR.md`.
Let `W` be the finite tangent group, let `q` be a central automorphism of
`W`, and let `alpha` be an automorphism with

`alpha^M=1`.                                            `(LCM3)`

The independent coordinate representations are `B_j(z)`, with indices in
`Z/MZ`.  They satisfy

`S_0 B_j(z) S_0^(-1)=B_(j+1)(alpha z)`,                `(LCM4)`

`[T,B_j(z)]=1` for `j!=0`,                             `(LCM5)`

`T B_0(z) T^(-1)=B_0(qz)`,                            `(LCM6)`

and

`S_1=S_0T^(-1)`.                                       `(LCM7)`

For `j!=0`, equations `(LCM4)--(LCM7)` give

`S_1 B_j(z) S_1^(-1)=B_(j+1)(alpha z)`.               `(LCM8)`

At the exceptional coordinate,

`S_1 B_0(z) S_1^(-1)=B_1(q^(-1)alpha z)`.             `(LCM9)`

Starting at coordinate one, the first `M-1` steps do not encounter the
exceptional conjugation.  The `M`-th step does.  Hence

`S_0^M B_1(z) S_0^(-M)=B_1(z)`,                       `(LCM10)`

`S_1^M B_1(z) S_1^(-M)=B_1(q^(-1)z)`.                `(LCM11)`

More generally, for `a>=0` and `0<=b<M`,

`Ad(S_0^(aM+b))(B_1(z))=B_(1+b)(alpha^b z)`,          `(LCM12)`

`Ad(S_1^(aM+b))(B_1(z))`
` =B_(1+b)(q^(-a)alpha^b z)`,                         `(LCM13)`

where coordinate indices are read modulo `M`.  This proves the accumulated
monodromy formula.

## 3. Compressor order

Let `r` be the order of `q` on `W`, and suppose the coordinate translation
representations are faithful and independent, as they are on
`ell^2(W^M)`.  If a positive power `S_1^ell` is scalar, its conjugation must
preserve the coordinate-one translation subgroup.  The coordinate shift
in `(LCM8)--(LCM9)` first forces

`M divides ell`.                                      `(LCM14)`

Write `ell=aM`.  Equation `(LCM13)` then forces

`q^a=1`,                                              `(LCM15)`

and therefore `r divides a`.  Thus

`M r divides ord_PU(S_1)`,                            `(LCM16)`

where `ord_PU` denotes projective unitary order.  In particular the actual
unitary order of `S_1` is also divisible by `M r`.

For `W` containing a primitive vector over `Z/p^nZ` and `q=1+p`, the
lifting-the-exponent identity

`v_p((1+p)^a-1)=1+v_p(a)`                             `(LCM17)`

shows that the order of `q` on that vector is exactly `p^(n-1)`.  This
proves `(LCM1)` and the lower bound

`M p^(n-1) divides ord_PU(S_1)`.                      `(LCM18)`

The finite-order statement in
`FALSE_PAIRED_FOURIER_PRINCIPAL_BUNDLE_SPLICE.md` is therefore correct but
quantitatively expensive: the order necessarily contains the full shear
order, not merely the depth-cycle order.

## 4. Agreement density in the coinduced bundle

Consider the subgroup prescription on one finite orbit of the external
transvection `t`.  If the orbit has length `L` and its fiber holonomy is
`S_i`, exactness requires

`S_i^L=1`.                                            `(LCM19)`

Equation `(LCM16)` implies that `L` is a multiple of `M r`.  Number the
orbit points as `t^(aM+b)x`, with `0<=b<M`.  In the naive coinduced model,
the two positive fiber representations are precisely the two sides of
`(LCM12)--(LCM13)`.  They agree on every tangent label exactly when

`q^a=1`.                                              `(LCM20)`

Among the `L` orbit points, this occurs at exactly `L/r` points.  The
agreement density is therefore

`1/r`.                                                `(LCM21)`

For a primitive marked label `z`, distinct translations in the regular
representation are Hilbert--Schmidt orthogonal.  At every point where
`q^a z!=z`,

`||B_j(z)-B_j(q^(-a)z)||_2^2=2`.                      `(LCM22)`

Averaging over the block-diagonal bundle gives

`||Pi_0(z)-Pi_1(z)||_2^2=2(1-1/r)`,                  `(LCM23)`

which specializes to `(LCM2)`.

Thus the phrase "take `M` to infinity" is insufficient after exact bundle
completion: both the common arc and the compulsory external orbit grow by
the same factor `M`, while the latter has the additional factor `r`.

## 5. Consequences for the live FALSE search

The finite equivariance equation `(LFE29)` remains the right endpoint, but
its solution cannot be the orbitwise coinduction of one long chain.  The
relative coefficient shear must be canceled before it becomes a global
positive-label mismatch.

Three possible escape mechanisms remain consistent with the monodromy
calculation:

1. **Higher-incidence holonomy-canceling codes.**  Couple many
   polarizations so the product shear around every external relator cycle
   is one, while marked evaluations meet many uncompensated walls.  Section
   6 below shows that a single bounded-degree cyclic wall system cannot do
   this.  The relevant statistic is the carry-row/marked-row incidence
   ratio from `FALSE_CARRY_MEAN_SUPPORT_FORMULA.md`.
2. **A nonconstant equivariant fiber functor.**  Solve `(LFE29)` with
   base-dependent tangent embeddings rather than conjugates of one seed
   embedding.  The embeddings must absorb `q^(-a)` while remaining equal on
   the growing polynomial window.
3. **An approximate, internally canceled external action.**  One may allow
   covariance error, but property `(T)` rules out concentrating it on a
   Følner-like boundary.  Cancellation must occur inside the tangent
   representation rather than by deleting a small part of the external
   orbit.

The first option is the most finite and computational, but only after the
one-dimensional conservation law below has been quotiented out.  A useful
search instance should no longer optimize dense unitaries.  It should
choose a sparse incidence matrix of Fourier walls subject to zero total
shear on each external relator cycle, then maximize the number of walls
seen by the marked evaluation relative to the maximum carry-row weight.  An
asymptotic family with carry/marked ratio tending to zero would evade
`(LCM23)` and feed directly into the existing sparse-carry/dense-word
certificate.

## 6. Balanced cyclic walls still cannot work

One might try to repair `(LCM11)` by inserting compensating inverse walls
elsewhere in the depth cycle.  There is an elementary support obstruction
to every such one-dimensional repair.

Let `C=Z/LZ`, let `A` be any abelian shear group, and let

`y:C->A`                                               `(LCM24)`

be the accumulated relative shear between the two sectors.  Its wall
increment is

`s(j)=y(j+1)-y(j)`.                                   `(LCM25)`

The total wall shear is automatically zero.  If `s(j)!=0`, then at least
one of `y(j),y(j+1)` is nonzero.  Every vertex is incident to at most two
cycle edges, hence

`|supp(s)| <= 2 |supp(y)|`.                           `(LCM26)`

In the regular translation/character model, a nonzero accumulated shear
gives squared positive-label discrepancy two, while a nonzero wall gives
at most squared marked-fold discrepancy two.  After normalization by `L`,

`E_marked <= 2 E_positive`.                           `(LCM27)`

Therefore `E_positive->0` forces `E_marked->0`.  Moving one compensating
wall far away, adding many pairs of opposite walls, or taking `L` to
infinity cannot change this conclusion.

The same support argument holds on a graph of maximum degree `Delta`:

`|supp(dy)| <= Delta |supp(y)|`.                      `(LCM28)`

Thus bounded-degree wall coboundaries cannot realize the required
low-carry/high-witness asymptotics.  A viable code must use at least one of
the following features:

1. marked rows whose incidence grows while carry rows stay sparse;
2. commutants which vary with the base point, so wall holonomy is invisible
   to the local positive representation without being an ordinary scalar
   coboundary; or
3. genuinely higher-dimensional or nonabelian derived data.

This is the precise search space left by `(LCM23)` and `(LCM26)`.
